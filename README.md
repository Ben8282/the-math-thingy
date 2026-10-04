# the-math-thingy

A fast, dependency-free **Goldbach conjecture verifier** written in x86-64
assembly (Linux and Windows, no libc, no compiler runtime).

> Goldbach's conjecture: every even integer greater than 2 is the sum of two primes.

It checks even numbers in order, finds a prime pair for each one, keeps a
record of the "hardest" numbers it meets, and checkpoints so you can stop and
resume. The whole program is one file: [`goldbach.asm`](goldbach.asm).

## Build

You only need [NASM](https://www.nasm.us/) and a linker.

```sh
# Linux
bash build.sh            # nasm -felf64 + ld  ->  ./goldbach

# Windows (nasm + GNU ld or lld-link on PATH)
build.cmd                # -> goldbach.exe
```

It runs on any x86-64 CPU. AVX2 and POPCNT are detected at startup and used
when present; otherwise it falls back to plain 64-bit code (`--baseline`
forces that).

## Use

```sh
./goldbach                           # start (or resume from checkpoint.txt), all cores
./goldbach --threads 8               # choose worker count
./goldbach --start 389965026819938   # begin at a specific number (rounded up to even)
./goldbach --until 10000000000       # verify up to N, then exit
./goldbach --log                     # write "N = p + q" lines to goldbach.txt (1 thread)
./goldbach --check                   # cross-check the vector path against a scalar path
```

While running, type a command: `status` (progress, rate, records), `stop`
(finish in-flight work, save a checkpoint, exit) or `quit` (exit now).
Ctrl-C is the same as `stop`.

Files it writes in the current directory:

| File | Contents |
|---|---|
| `checkpoint.txt` | verified-up-to bound and statistics; read on startup to resume (written atomically) |
| `interesting_cases.txt` | each new "most difficult number" (needed the largest prime `p`) |
| `violations.txt` | any even number with no prime pair. It should stay empty. |
| `goldbach.txt` | `N = p + q` lines, only with `--log` |

"Checks" counts `pi(p)` for the smallest prime `p` that works, so `2 -> 1`,
`3 -> 2`, `5 -> 3`, ...

Example: `389965026819938 = 5569 + 389965026814369`, found after 735 checks.

```sh
./goldbach --start 389965026819938 --until 389965026819938
```

## How it works

1. Even numbers are processed in chunks of 133,693,440, spread over worker
   threads that claim chunks with an atomic counter.
2. Each chunk is 32 segments; a segment is a 256 KB bitmap of odd numbers
   (fits in L2). A segmented sieve of Eratosthenes marks the composites.
3. **Word-parallel Goldbach pass.** For an odd prime `p`, the even numbers `N`
   where `N - p` is prime are just the prime bitmap shifted by a constant. So
   one AVX2 instruction tests 256 numbers against `p` at once, and passes run
   until every number in the segment has a partner.
4. The rare stragglers are finished one by one; anything that still has no
   partner among the primes up to 16385 goes to an exhaustive search using
   deterministic Miller-Rabin (never needed in practice).
5. The base prime table starts at 2^26 and doubles when needed, up to 2^32, so
   every 64-bit `N` is covered. The only limit is the 64-bit integer range
   (`N <= 2^64 - 2`).
6. Chunk results are merged strictly in order of `N`, so records and
   checkpoints are deterministic regardless of thread timing.

## Speed, and why the old C++ and Python versions were retired

This project started as a C++ program (`main.cpp`) and a Python port
(`main.py`). Both are still available on the
[`legacy-cpp-python`](../../tree/legacy-cpp-python) branch, but they are not
maintained and are much slower. Rough numbers from one run on a 4-core Linux
sandbox, verifying from 4 upwards (not a rigorous benchmark; your hardware
will differ):

| Version | Throughput | Time to verify up to 10^10 |
|---|---|---|
| `goldbach.asm` (AVX2, 4 threads) | ~3 billion even numbers / s | ~3 s |
| `main.cpp` (`-O2`, 4 threads) | ~1.8 million / s | ~1.5 hours (extrapolated) |
| `main.py` (4 processes) | ~0.4 million / s | ~7 hours (extrapolated) |

Why they are slow: they test candidate pairs one number at a time with
Miller-Rabin and a list of ~114,000 small primes, and they run a separate prime
enumerator. The assembly version instead resolves hundreds of numbers per
instruction using the sieve bitmap directly. The legacy versions are also
limited in other ways, for example their displayed prime count is only
accurate up to about 2.25e12.

## Correctness

- `--check` runs the AVX2 path and an independent scalar path on every segment
  and aborts on any mismatch. Verifying up to ~10^9 with `--check` passes.
- Miller-Rabin uses the witness set {2..37}, proven deterministic for all
  64-bit integers.
- This program verifies the conjecture for a range of numbers. It does not,
  and cannot, prove it. Results come from a program, so treat extreme-range
  claims with appropriate scepticism and cross-check with `--check`.

## License

You may use this project under **any one** of these licenses, at your option:

- [MIT](LICENSE-MIT)
- [Apache License 2.0](LICENSE-APACHE)
- [GNU GPL v2](LICENSE-GPL-2.0) (`GPL-2.0-only`)
- [GNU GPL v3](LICENSE-GPL-3.0) (`GPL-3.0-only`)

SPDX: `MIT OR Apache-2.0 OR GPL-2.0-only OR GPL-3.0-only`

Note: earlier revisions of this repository carried a single `LICENSE` file
(Apache 2.0). The licensing above applies going forward.
