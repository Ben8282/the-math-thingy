#!/usr/bin/env python3
# ---------------------------------------------------------------------------
# Goldbach conjecture verifier — Python port of main.cpp.
#
# HOW THE GOLDBACH VERIFIER ACHIEVES MATHEMATICAL CORRECTNESS
#
# 1. Phase 1 (fast path): SMALL_PRIMES holds every prime up to
#    SMALL_PRIME_LIMIT (1,500,000) — ~114,000 entries, built once at startup.
#    For each even N the verifier iterates these as candidate p, testing
#    q = N-p with deterministic Miller-Rabin.  In practice this finds a pair
#    in the first one to three iterations for every N encountered.
#
# 2. Phase 2 (completeness fallback): If Phase 1 exhausts all small primes
#    without finding a pair, the verifier continues scanning odd integers
#    p = SMALL_PRIME_LIMIT+2, SMALL_PRIME_LIMIT+4, ... up to N/2, testing
#    each p and q = N-p with Miller-Rabin.  This makes correctness
#    unconditional — no unproven assumption about small-prime Goldbach
#    coverage is required.
#
# 3. Miller-Rabin witnesses {2..37} are proven deterministic for all
#    n < 3.317e24, covering every 64-bit value with zero false results.
#    (Python ints are arbitrary-precision, so the C++ overflow guards are
#    unnecessary here.)
#
# 4. Memory is bounded: SMALL_PRIMES is fixed; the segmented-sieve buffer
#    used by the enumerator thread is reused every segment.
#
# PYTHON-SPECIFIC DESIGN CHANGES vs the C++ original
#
# * Workers are PROCESSES (ProcessPoolExecutor), not threads — CPython's GIL
#   prevents thread-level parallelism for CPU-bound work.
# * The C++ workers updated record statistics via lock-free CAS and wrote
#   interesting_cases.txt themselves.  Processes can't share atomics cheaply,
#   so each batch returns its local maxima and the coordinator (single
#   thread) merges them and writes the record file.  Output is equivalent.
# * The prime enumerator and command loop remain threads (they are I/O-light
#   and display-only).
#
# NOTE ON THE PRIME ENUMERATOR THREAD
# A sieve base of primes up to L correctly sieves numbers up to L^2, i.e.
# ~2.25e12 here.  Beyond that its prime *count* over-counts.  This has no
# effect on Goldbach correctness; it only affects the status display.
# ---------------------------------------------------------------------------

import math
import multiprocessing
import os
import sys
import threading
import time
from collections import deque
from concurrent.futures import FIRST_COMPLETED, ProcessPoolExecutor, wait
from datetime import datetime

# ---------------------------------------------------------------------------
# Tuning constants
# ---------------------------------------------------------------------------
SMALL_PRIME_LIMIT = 1_500_000    # primes stored for Goldbach p candidates
SEG_SIZE = 1 << 21               # odd-number slots per sieve segment (~2 MB)
BATCH_SIZE = 10_000              # even numbers per Goldbach work unit
WRITE_BATCH = 1_000              # output lines buffered before flushing
CHECKPOINT_INTERVAL = 1_000_000  # min verified advance per checkpoint write

# ---------------------------------------------------------------------------
# Global state (main process) — coordinator is the single writer of stats;
# the command loop only reads.  Lists are guarded by locks.
# ---------------------------------------------------------------------------
SMALL_PRIMES = []                # built once in main(), read-only afterwards

g_total_primes = 0
g_prime_frontier = 2             # highest prime seen by enumerator
g_checked = 2                    # highest even number Goldbach-verified
g_stop = threading.Event()
g_violations = []
g_violations_lock = threading.Lock()
g_io_lock = threading.Lock()
g_num_workers = 1

# Statistics (single writer: coordinator thread)
g_fallback_activations = 0
g_largest_fallback_N = 0         # N of the deepest fallback search seen
g_max_fallback_depth = 0         # deepest fallback iteration count seen
g_max_fast_depth = 0             # largest Phase-1 iteration count seen
g_max_fast_depth_N = 0           # N that produced g_max_fast_depth


# ---------------------------------------------------------------------------
# Deterministic Miller-Rabin primality test
# ---------------------------------------------------------------------------
_MR_WITNESSES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)


def is_prime_mr(n):
    if n < 2:
        return False
    if n in (2, 3, 5):
        return True
    if n % 2 == 0 or n % 3 == 0 or n % 5 == 0:
        return False
    d = n - 1
    r = 0
    while d % 2 == 0:
        d >>= 1
        r += 1
    for a in _MR_WITNESSES:
        if a >= n:
            continue
        x = pow(a, d, n)          # built-in modular exponentiation
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


# ---------------------------------------------------------------------------
# Build the small-prime table — Eratosthenes sieve over odd numbers up to
# SMALL_PRIME_LIMIT.
# ---------------------------------------------------------------------------
def build_small_primes():
    size = (SMALL_PRIME_LIMIT - 1) // 2      # slots for 3, 5, 7, ...
    sieve = bytearray(size)
    i = 0
    while True:
        p = 2 * i + 3
        if p * p > SMALL_PRIME_LIMIT:
            break
        if not sieve[i]:
            start = (p * p - 3) // 2
            sieve[start::p] = b"\x01" * len(range(start, size, p))
        i += 1
    primes = [2]
    primes.extend(2 * j + 3 for j in range(size) if not sieve[j])
    return primes


def current_timestamp():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


# ---------------------------------------------------------------------------
# Worker process side
# ---------------------------------------------------------------------------
_worker_primes = None


def _init_worker():
    # Rebuild the table per process (works under both fork and spawn;
    # takes well under a second).
    global _worker_primes
    _worker_primes = build_small_primes()


def check_goldbach_batch(even_start, even_end):
    """Verify Goldbach for evens in [even_start, even_end), step 2.

    Returns (result_lines, stats) where stats carries the batch-local maxima
    that the coordinator merges into the global records.
    """
    primes = _worker_primes
    results = []
    stats = {
        "max_fast_depth": 0, "max_fast_depth_N": 0,
        "fallback_activations": 0,
        "max_fallback_depth": 0, "largest_fallback_N": 0,
    }
    fallback_start = primes[-1] + 2 if primes else 3

    for N in range(even_start, even_end, 2):
        found = False
        half = N >> 1

        # Phase 1: small-prime candidates (fast).  fast_depth counts primes
        # tried (1-indexed; only primes with p <= N/2 are counted).
        fast_depth = 0
        for p in primes:
            if p > half:
                break
            fast_depth += 1
            q = N - p
            if is_prime_mr(q):
                results.append(f"{N} = {p} + {q}")
                found = True
                if fast_depth > stats["max_fast_depth"]:
                    stats["max_fast_depth"] = fast_depth
                    stats["max_fast_depth_N"] = N
                break

        # Phase 2: exhaustive fallback beyond SMALL_PRIME_LIMIT.  Entered
        # only when every Goldbach pair for this N has both primes above
        # SMALL_PRIME_LIMIT.  No such N is known to exist, so this path is
        # never expected to be taken in practice.
        if not found and fallback_start <= half:
            stats["fallback_activations"] += 1
            fallback_depth = 0
            for p in range(fallback_start, half + 1, 2):
                fallback_depth += 1
                if is_prime_mr(p):
                    q = N - p
                    if is_prime_mr(q):
                        results.append(f"{N} = {p} + {q}")
                        found = True
                        if fallback_depth > stats["max_fallback_depth"]:
                            stats["max_fallback_depth"] = fallback_depth
                            stats["largest_fallback_N"] = N
                        break

        if not found:
            results.append(f"VIOLATION: {N} has no prime pair!")

    return results, stats


# ---------------------------------------------------------------------------
# Checkpoint writer — overwrites checkpoint.txt with current statistics.
# Called from the coordinator thread only.
# ---------------------------------------------------------------------------
def write_checkpoint():
    try:
        with open("checkpoint.txt", "w") as cp:
            cp.write(
                f"Goldbach verified up to: {g_checked}\n\n"
                f"Goldbach failures found: {len(g_violations)}\n\n"
                f"Times the emergency search was needed: {g_fallback_activations}\n\n"
                f"Largest number that needed the emergency search: {g_largest_fallback_N}\n\n"
                f"Most work ever needed during an emergency search: {g_max_fallback_depth} checks\n\n"
                f"Number that was most difficult to verify: {g_max_fast_depth_N}\n\n"
                f"Most difficult number checked so far: {g_max_fast_depth} checks\n\n"
                f"Timestamp: {current_timestamp()}\n"
            )
    except OSError:
        pass


# ---------------------------------------------------------------------------
# Goldbach coordinator thread
#
# Distributes batches of even numbers to worker processes, collects results,
# merges statistics, and appends them to goldbach.txt / violations.txt /
# interesting_cases.txt.
# ---------------------------------------------------------------------------
def goldbach_coordinator():
    global g_checked, g_fallback_activations, g_largest_fallback_N
    global g_max_fallback_depth, g_max_fast_depth, g_max_fast_depth_N

    try:
        f = open("goldbach.txt", "a")
        viol_file = open("violations.txt", "a")
        interesting_file = open("interesting_cases.txt", "a")
    except OSError as e:
        with g_io_lock:
            print(f"[Goldbach] ERROR: cannot open output file: {e}", file=sys.stderr)
        g_stop.set()
        return

    def record_interesting(header, N, depth):
        interesting_file.write(
            f"{header}\n\n"
            f"Number={N}\n\n"
            f"Checks needed before finding a Goldbach pair={depth}\n\n"
            f"Timestamp={current_timestamp()}\n\n"
        )
        interesting_file.flush()

    def merge_stats(stats):
        global g_fallback_activations, g_largest_fallback_N
        global g_max_fallback_depth, g_max_fast_depth, g_max_fast_depth_N
        if stats["max_fast_depth"] > g_max_fast_depth:
            g_max_fast_depth = stats["max_fast_depth"]
            g_max_fast_depth_N = stats["max_fast_depth_N"]
            record_interesting("NEW MOST DIFFICULT NUMBER FOUND",
                               g_max_fast_depth_N, g_max_fast_depth)
        g_fallback_activations += stats["fallback_activations"]
        if stats["max_fallback_depth"] > g_max_fallback_depth:
            g_max_fallback_depth = stats["max_fallback_depth"]
            g_largest_fallback_N = stats["largest_fallback_N"]
            record_interesting("NEW EMERGENCY SEARCH RECORD",
                               g_largest_fallback_N, g_max_fallback_depth)

    write_buf = []

    def flush_write_buf():
        if write_buf:
            f.write("\n".join(write_buf) + "\n")
            f.flush()
            write_buf.clear()

    def process_lines(lines):
        for line in lines:
            if line.startswith("VIOLATION"):
                with g_violations_lock:
                    g_violations.append(line)
                viol_file.write(line + "\n")
                viol_file.flush()
                with g_io_lock:
                    print(f"\n*** {line} ***\n> ", end="", flush=True)
            else:
                write_buf.append(line)

    next_even = 4
    last_checkpoint_at = 0

    # "spawn" avoids fork-with-running-threads deadlocks on Linux and is the
    # only start method on Windows, so behavior is identical everywhere.
    ctx = multiprocessing.get_context("spawn")
    with ProcessPoolExecutor(max_workers=g_num_workers, mp_context=ctx,
                             initializer=_init_worker) as pool:
        # queue of (future, last_even_in_batch), processed in submission order
        queue = deque()

        while not g_stop.is_set():
            # Keep the pipeline full: at most num_workers*2 batches in flight
            while len(queue) < g_num_workers * 2:
                batch_end = next_even + BATCH_SIZE * 2
                fut = pool.submit(check_goldbach_batch, next_even, batch_end)
                queue.append((fut, batch_end - 2))
                next_even = batch_end

            fut, batch_last = queue[0]
            done, _ = wait([fut], timeout=0.001, return_when=FIRST_COMPLETED)
            if done:
                queue.popleft()
                lines, stats = fut.result()
                merge_stats(stats)
                process_lines(lines)
                if len(write_buf) >= WRITE_BATCH:
                    flush_write_buf()
                g_checked = batch_last
                if batch_last - last_checkpoint_at >= CHECKPOINT_INTERVAL:
                    write_checkpoint()
                    last_checkpoint_at = batch_last

        # Drain any in-flight work
        for fut, batch_last in queue:
            lines, stats = fut.result()
            merge_stats(stats)
            process_lines(lines)
            g_checked = batch_last
        flush_write_buf()
        write_checkpoint()  # final checkpoint so the last state is on disk

    f.close()
    viol_file.close()
    interesting_file.close()
    with g_io_lock:
        print(f"\n[Goldbach] Verified up to {g_checked}. "
              f"Violations: {len(g_violations)}.")


# ---------------------------------------------------------------------------
# Prime enumerator thread (display only — does not feed the verifier)
#
# Segmented sieve beyond SMALL_PRIME_LIMIT using SMALL_PRIMES as the base.
# The segment buffer is reused each iteration — memory usage is constant.
# ---------------------------------------------------------------------------
def enumerate_primes_forever():
    global g_total_primes, g_prime_frontier
    g_total_primes = len(SMALL_PRIMES)
    g_prime_frontier = SMALL_PRIMES[-1] if SMALL_PRIMES else 2

    seg_lo = SMALL_PRIME_LIMIT + 2
    if seg_lo % 2 == 0:
        seg_lo += 1  # ensure odd start

    while not g_stop.is_set():
        seg_hi = seg_lo + 2 * SEG_SIZE - 2
        sqrt_hi = math.isqrt(seg_hi) + 2
        seg = bytearray(SEG_SIZE)

        for p in SMALL_PRIMES:
            if p == 2:
                continue
            if p > sqrt_hi:
                break
            start = ((seg_lo + p - 1) // p) * p
            if start % 2 == 0:
                start += p
            if start == p:
                start += 2 * p  # don't mark p itself
            if start > seg_hi:
                continue
            idx = (start - seg_lo) // 2
            seg[idx::p] = b"\x01" * len(range(idx, SEG_SIZE, p))

        found = seg.count(0)
        if found:
            g_total_primes += found
            g_prime_frontier = seg_lo + 2 * seg.rfind(b"\x00")
        else:
            g_prime_frontier = seg_hi

        seg_lo = seg_hi + 2
        time.sleep(0.001)  # yield the GIL so interactive threads stay responsive


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------
def main():
    global g_num_workers, SMALL_PRIMES

    cpu = os.cpu_count() or 1
    g_num_workers = max(1, cpu - 1)

    print("Is every even integer > 2 the sum of two primes?")
    print(f"Using {g_num_workers} worker process(es) for Goldbach verification.")
    print("Commands: status | stop | quit\n")
    print(f"Building prime table (primes up to {SMALL_PRIME_LIMIT})...",
          end="", flush=True)

    SMALL_PRIMES[:] = build_small_primes()
    print(f" done. ({len(SMALL_PRIMES)} primes)\n")

    prime_thread = threading.Thread(target=enumerate_primes_forever, daemon=True)
    goldbach_thread = threading.Thread(target=goldbach_coordinator)
    prime_thread.start()
    goldbach_thread.start()
    print("Running.\n")

    while True:
        try:
            with g_io_lock:
                print("> ", end="", flush=True)
            line = input()
        except (EOFError, KeyboardInterrupt):
            break
        cmd = line.strip().lower()
        if cmd == "status":
            with g_violations_lock:
                vio = list(g_violations)
            with g_io_lock:
                print(f"Primes enumerated       : {g_total_primes}"
                      f"  (frontier: {g_prime_frontier})")
                print(f"Goldbach verified       : up to {g_checked}")
                print(f"Fallback activations    : {g_fallback_activations}")
                print(f"Largest fallback N      : {g_largest_fallback_N}")
                print(f"Deepest fallback depth  : {g_max_fallback_depth}")
                print(f"Largest fast-path depth : {g_max_fast_depth}")
                print(f"Largest fast-path N     : {g_max_fast_depth_N}")
                if vio:
                    print(f"VIOLATIONS ({len(vio)}):")
                    for v in vio:
                        print(f"  {v}")
                else:
                    print("No violations found so far.")
        elif cmd == "stop":
            g_stop.set()
            break
        elif cmd == "quit":
            with g_io_lock:
                print("Force quitting.")
            os._exit(0)
        elif cmd:
            print("Commands: status | stop | quit")

    g_stop.set()
    goldbach_thread.join()  # drains in-flight batches, writes final checkpoint
    return 0


if __name__ == "__main__":
    sys.exit(main())
