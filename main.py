import os
import threading
import time
import multiprocessing
from concurrent.futures import ProcessPoolExecutor

BATCH_SIZE = 10000
# Use the CPUs available to this process (including any OS/container limit),
# while reserving one for prime generation and the command prompt.
CPU_COUNT = os.process_cpu_count() or 1
NUM_WORKERS = max(1, CPU_COUNT - 1)


def is_prime(n):
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(n**0.5) + 1, 2):
        if n % i == 0:
            return False
    return True


def check_goldbach_batch(args):
    evens, primes_list = args
    primes_set = set(primes_list)
    results = []
    for even in evens:
        found = False
        for p in primes_list:
            if p > even // 2:
                break
            if (even - p) in primes_set:
                results.append(f"{even} = {p} + {even - p}")
                found = True
                break
        if not found:
            results.append(f"VIOLATION: {even} has no prime pair!")
    return results


if __name__ == "__main__":
    print("is it true that all even numbers greater than 2 are a sum of 2 prime numbers")
    print(f"Using {NUM_WORKERS} worker processes for Goldbach verification.")
    print("Type 'status' to check progress, 'stop' to stop, or 'quit' to force quit.\n")

    stop_event = threading.Event()
    primes = [2]
    primes_set = {2}
    current = 3
    goldbach_checked = 3
    violations = []

    def generate_primes_forever():
        global current
        os.path.exists("primes.txt")
        with open("primes.txt", "a") as f:
            while not stop_event.is_set():
                if is_prime(current):
                    primes.append(current)
                    primes_set.add(current)
                    f.write(f"{current}\n")
                    f.flush()
                current += 2
        print(f"\n[Primes] Found {len(primes)} primes up to {current}.")

    def goldbach_coordinator():
        global goldbach_checked
        next_even = 4
        os.path.exists("goldbach.txt")
        with ProcessPoolExecutor(max_workers=NUM_WORKERS) as executor, \
             open("goldbach.txt", "a") as f:
            queue = []

            while not stop_event.is_set():
                batch_end = next_even + BATCH_SIZE * 2

                # Submit new batches whenever primes cover the range and queue has room
                while len(queue) < NUM_WORKERS * 2 and current > batch_end:
                    snapshot = [p for p in primes if p <= batch_end]
                    batch = list(range(next_even, batch_end, 2))
                    fut = executor.submit(check_goldbach_batch, (batch, snapshot))
                    queue.append((fut, batch_end - 2))
                    next_even = batch_end
                    batch_end = next_even + BATCH_SIZE * 2

                # Collect the oldest future in order so the file stays sequential
                if queue and queue[0][0].done():
                    fut, last_even = queue.pop(0)
                    for line in fut.result():
                        f.write(line + "\n")
                        if line.startswith("VIOLATION"):
                            violations.append(line)
                            print(f"\n*** {line} ***\n> ", end="", flush=True)
                    f.flush()
                    goldbach_checked = last_even
                else:
                    time.sleep(0.001)

            # Drain remaining futures on stop
            for fut, last_even in queue:
                for line in fut.result():
                    f.write(line + "\n")
                    if line.startswith("VIOLATION"):
                        violations.append(line)
                f.flush()
                goldbach_checked = last_even

        print(f"\n[Goldbach] Verified up to {goldbach_checked}. Violations: {len(violations)}.")

    prime_thread = threading.Thread(target=generate_primes_forever, daemon=True)
    goldbach_thread = threading.Thread(target=goldbach_coordinator, daemon=True)
    prime_thread.start()
    goldbach_thread.start()
    print("Prime generation and Goldbach verification started...\n")

    while True:
        cmd = input("> ").strip().lower()
        if cmd == "status":
            print(f"Primes: {len(primes)} found, checking up to {current}.")
            print(f"Goldbach: verified up to {goldbach_checked}.")
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
            break
        elif cmd == "quit":
            print("Force quitting...")
            os._exit(0)
        elif cmd:
            print("Commands: status | stop | quit")
