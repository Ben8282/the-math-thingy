import os
import threading
import time
import multiprocessing
from concurrent.futures import ProcessPoolExecutor
from multiprocessing.shared_memory import SharedMemory

BATCH_SIZE    = 10_000         # even numbers per Goldbach worker batch
WRITE_BATCH   = 1_000          # primes collected before one flush to disk
SEGMENT_SIZE  = 1 << 21        # 2 M odd slots = ~4 M number range per segment
SMALL_PRIME_LIMIT = 1_000_000  # small primes cached for segment sieve (covers to 10^12)

CPU_COUNT   = os.process_cpu_count() or 1
NUM_WORKERS = max(1, CPU_COUNT - 1)

SIEVE_LIMIT = 100_000_000
MAX_PRIMES  = 10_000_000   # uint32 slots; covers primes up to ~250 M


def is_prime(n):
    """Trial-division fallback — only reached for q > SIEVE_LIMIT inside workers."""
    if n < 2: return False
    if n == 2: return True
    if n % 2 == 0: return False
    for i in range(3, int(n**0.5) + 1, 2):
        if n % i == 0: return False
    return True


def _odd_sieve(limit):
    """
    Odd-only Sieve of Eratosthenes to `limit`.
    Index i -> odd number 2*i+3.  0 = prime, 1 = composite.
    """
    size = (limit - 1) // 2
    sieve = bytearray(size)
    i = 0
    while True:
        p = 2 * i + 3
        if p * p > limit:
            break
        if not sieve[i]:
            start = (p * p - 3) // 2
            n_marks = (size - start + p - 1) // p
            sieve[start::p] = b'\x01' * n_marks
        i += 1
    return sieve


def _segment_sieve(seg_lo, seg_hi, small_primes):
    """
    Segmented odd-only sieve — returns all primes in [seg_lo, seg_hi].

    seg_lo must be odd.
    small_primes must contain all primes <= sqrt(seg_hi).

    p=2 is skipped: the segment stores only odd numbers, so 2 has no odd
    multiples to mark.  Including it corrupts the index arithmetic.
    """
    size = (seg_hi - seg_lo) // 2 + 1
    sieve = bytearray(size)
    for p in small_primes:
        if p == 2:
            continue          # odd-only segment; 2 has no odd multiples here
        # First odd multiple of p that is >= seg_lo
        start = ((seg_lo + p - 1) // p) * p   # ceil(seg_lo / p) * p
        if start % 2 == 0:
            start += p        # p is odd -> even + odd = odd
        if start == p:
            start += 2 * p   # skip p itself
        if start > seg_hi:
            continue
        start_idx = (start - seg_lo) // 2
        n_marks   = (size - start_idx + p - 1) // p
        sieve[start_idx::p] = b'\x01' * n_marks
    return [seg_lo + 2 * i for i, c in enumerate(sieve) if not c]


def check_goldbach_batch(args):
    """
    Worker — runs in a separate OS process.
    Receives only small scalars; attaches to shared memory for prime data.
    Uses the sieve byte array for O(1) membership; no set is ever built.
    """
    even_start, even_end, n_primes, primes_shm_name, sieve_shm_name, sieve_slots = args
    shm_p = SharedMemory(name=primes_shm_name)
    shm_s = SharedMemory(name=sieve_shm_name)
    p_buf = memoryview(shm_p.buf).cast('I')
    s_buf = memoryview(shm_s.buf)
    results = []
    for even in range(even_start, even_end, 2):
        found = False
        half  = even >> 1
        for i in range(n_primes):
            p = p_buf[i]
            if p > half:
                break
            q = even - p
            if q == 2:
                is_q_prime = True
            elif q < 3 or not (q & 1):
                is_q_prime = False
            else:
                q_idx = (q - 3) >> 1
                is_q_prime = (s_buf[q_idx] == 0) if q_idx < sieve_slots else is_prime(q)
            if is_q_prime:
                results.append(f"{even} = {p} + {q}")
                found = True
                break
        if not found:
            results.append(f"VIOLATION: {even} has no prime pair!")
    del p_buf, s_buf
    shm_p.close()
    shm_s.close()
    return results


if __name__ == "__main__":
    print("is it true that all even numbers greater than 2 are a sum of 2 prime numbers")
    print(f"Using {NUM_WORKERS} worker processes for Goldbach verification.")
    print("Type 'status' to check progress, 'stop' to stop, or 'quit' to force quit.")

    print("Computing sieve and initialising shared memory...", end="", flush=True)
    _sieve = _odd_sieve(SIEVE_LIMIT)
    sieve_slots = len(_sieve)

    shm_sieve = SharedMemory(create=True, size=sieve_slots)
    shm_sieve.buf[:sieve_slots] = _sieve
    del _sieve

    shm_primes = SharedMemory(create=True, size=MAX_PRIMES * 4)
    _pv = memoryview(shm_primes.buf).cast('I')
    _pv[0] = 2
    del _pv
    shm_count = multiprocessing.Value('L', 1)
    print(" done.\n")

    stop_event      = threading.Event()
    primes          = [2]
    current         = 3
    goldbach_checked = [3]   # list so mutation is visible across threads
    violations      = []

    def generate_primes_forever():
        global current
        pv  = memoryview(shm_primes.buf).cast('I')
        sv  = memoryview(shm_sieve.buf)
        idx = shm_count.value

        # Small primes from the initial sieve, used as the basis for
        # the segmented sieve in Phase 2.  Covers segments up to ~10^12.
        small_primes = []

        os.path.exists("primes.txt")
        with open("primes.txt", "a") as f:
            write_buf = []

            # ── Phase 1: stream the pre-computed 100M sieve ───────────────────
            for slot_idx, composite in enumerate(sv):
                if stop_event.is_set():
                    break
                n = 2 * slot_idx + 3
                current = n
                if not composite:
                    primes.append(n)
                    if n <= SMALL_PRIME_LIMIT:
                        small_primes.append(n)
                    if idx < MAX_PRIMES:
                        pv[idx] = n
                        idx += 1
                    write_buf.append(f"{n}\n")
                    if len(write_buf) >= WRITE_BATCH:
                        f.write(''.join(write_buf))
                        f.flush()
                        shm_count.value = idx   # batch update reduces lock contention
                        write_buf.clear()
                # Yield GIL so the coordinator thread gets CPU time.
                if slot_idx % 50_000 == 0:
                    time.sleep(0)

            if write_buf:
                f.write(''.join(write_buf))
                f.flush()
                shm_count.value = idx
                write_buf.clear()

            # ── Phase 2: segmented sieve beyond SIEVE_LIMIT ───────────────────
            # Replaces trial division entirely.  Maintains ~sieve-level
            # throughput indefinitely — no per-candidate sqrt() checks.
            if not stop_event.is_set():
                seg_lo = SIEVE_LIMIT + 1
                if seg_lo % 2 == 0:
                    seg_lo += 1

                while not stop_event.is_set():
                    seg_hi    = seg_lo + SEGMENT_SIZE * 2 - 2
                    sqrt_hi   = int(seg_hi ** 0.5) + 1
                    seg_small = [p for p in small_primes if p <= sqrt_hi]

                    seg_primes = _segment_sieve(seg_lo, seg_hi, seg_small)

                    for p in seg_primes:
                        if stop_event.is_set():
                            break
                        current = p
                        primes.append(p)
                        if idx < MAX_PRIMES:
                            pv[idx] = p
                            idx += 1
                        write_buf.append(f"{p}\n")
                        if len(write_buf) >= WRITE_BATCH:
                            f.write(''.join(write_buf))
                            f.flush()
                            shm_count.value = idx
                            write_buf.clear()

                    if not seg_primes:
                        current = seg_hi   # advance current even in sparse zones

                    seg_lo = seg_hi + 2

            if write_buf:
                f.write(''.join(write_buf))
                f.flush()
                shm_count.value = idx

        del pv, sv
        print(f"\n[Primes] Found {len(primes)} primes up to {current}.")

    def goldbach_coordinator():
        next_even = 4
        p_name  = shm_primes.name
        s_name  = shm_sieve.name
        s_slots = sieve_slots

        os.path.exists("goldbach.txt")
        with ProcessPoolExecutor(max_workers=NUM_WORKERS) as executor, \
             open("goldbach.txt", "a") as f:
            queue = []

            while not stop_event.is_set():
                batch_end = next_even + BATCH_SIZE * 2

                while len(queue) < NUM_WORKERS * 2 and current > batch_end:
                    n_p  = shm_count.value
                    args = (next_even, batch_end, n_p, p_name, s_name, s_slots)
                    fut  = executor.submit(check_goldbach_batch, args)
                    queue.append((fut, batch_end - 2))
                    next_even = batch_end
                    batch_end = next_even + BATCH_SIZE * 2

                if queue and queue[0][0].done():
                    fut, last_even = queue.pop(0)
                    for line in fut.result():
                        f.write(line + "\n")
                        if line.startswith("VIOLATION"):
                            violations.append(line)
                            print(f"\n*** {line} ***\n> ", end="", flush=True)
                    f.flush()
                    goldbach_checked[0] = last_even
                else:
                    time.sleep(0.0005)   # 0.5 ms — tighter poll than before

            for fut, last_even in queue:
                for line in fut.result():
                    f.write(line + "\n")
                    if line.startswith("VIOLATION"):
                        violations.append(line)
                f.flush()
                goldbach_checked[0] = last_even

        print(f"\n[Goldbach] Verified up to {goldbach_checked[0]}. Violations: {len(violations)}.")

    prime_thread    = threading.Thread(target=generate_primes_forever, daemon=True)
    goldbach_thread = threading.Thread(target=goldbach_coordinator,    daemon=True)
    prime_thread.start()
    goldbach_thread.start()
    print("Prime generation and Goldbach verification started.\n")

    while True:
        cmd = input("> ").strip().lower()
        if cmd == "status":
            print(f"Primes: {len(primes)} found, checking up to {current}.")
            print(f"Goldbach: verified up to {goldbach_checked[0]}.")
            if violations:
                print(f"VIOLATIONS: {len(violations)}")
                for v in violations:
                    print(f"  {v}")
            else:
                print("No violations found so far.")
        elif cmd == "stop":
            stop_event.set()
            prime_thread.join()
            goldbach_thread.join()
            shm_primes.close(); shm_primes.unlink()
            shm_sieve.close();  shm_sieve.unlink()
            break
        elif cmd == "quit":
            print("Force quitting...")
            os._exit(0)
        elif cmd:
            print("Commands: status | stop | quit")
