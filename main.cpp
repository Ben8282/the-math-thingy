#include <cstdint>
#include <cstdlib>
#include <cmath>
#include <cctype>
#include <string>
#include <vector>
#include <deque>
#include <queue>
#include <atomic>
#include <thread>
#include <mutex>
#include <condition_variable>
#include <future>
#include <functional>
#include <memory>
#include <fstream>
#include <iostream>
#include <chrono>
#include <algorithm>
#include <utility>
#include <initializer_list>
#include <ctime>

// ---------------------------------------------------------------------------
// Tuning constants
// ---------------------------------------------------------------------------
constexpr uint64_t    SMALL_PRIME_LIMIT = 1'500'000; // primes stored for Goldbach p candidates
constexpr uint64_t    SEG_SIZE          = 1ull << 21; // odd-number slots per sieve segment (~2 MB)
constexpr uint64_t    BATCH_SIZE        = 10'000;     // even numbers per Goldbach work unit
constexpr std::size_t WRITE_BATCH         = 1'000;      // output lines buffered before flushing
constexpr uint64_t    CHECKPOINT_INTERVAL = 1'000'000;  // min verified advance per checkpoint write

// ---------------------------------------------------------------------------
// Global state — all structures are fixed-size or O(in-flight batches only)
// ---------------------------------------------------------------------------
static std::vector<uint32_t> g_small_primes;           // ≤ SMALL_PRIME_LIMIT, never grows
static std::atomic<uint64_t> g_total_primes{0};
static std::atomic<uint64_t> g_prime_frontier{2};      // highest prime seen by enumerator
static std::atomic<uint64_t> g_checked{2};             // highest even number Goldbach-verified
static std::atomic<bool>     g_stop{false};
static std::vector<std::string> g_violations;
static std::atomic<uint64_t>    g_violation_count{0};   // mirrors g_violations.size(); atomic for checkpoint reads
static std::ofstream g_viol_file;        // violations.txt        — guarded by g_violations_mtx
static std::mutex g_violations_mtx;
static std::mutex g_io_mtx;
static unsigned g_num_workers = 1;

// ---------------------------------------------------------------------------
// Statistics — updated from worker threads via lock-free CAS; readable
// from any thread without a lock.
// ---------------------------------------------------------------------------
static std::atomic<uint64_t> g_fallback_activations{0};
static std::atomic<uint64_t> g_largest_fallback_N{0};   // N of the deepest fallback search seen
static std::atomic<uint64_t> g_max_fallback_depth{0};   // deepest fallback iteration count seen
static std::atomic<uint64_t> g_max_fast_depth{0};       // largest Phase-1 iteration count seen
static std::atomic<uint64_t> g_max_fast_depth_N{0};     // N that produced g_max_fast_depth
static std::ofstream g_interesting_file; // interesting_cases.txt — guarded by g_interesting_mtx
static std::mutex    g_interesting_mtx;

// ---------------------------------------------------------------------------
// ThreadPool
// ---------------------------------------------------------------------------
class ThreadPool {
public:
    explicit ThreadPool(std::size_t n) {
        for (std::size_t i = 0; i < n; ++i)
            workers.emplace_back([this] { worker_loop(); });
    }
    ~ThreadPool() {
        { std::unique_lock<std::mutex> lk(m); stopping = true; }
        cv.notify_all();
        for (auto &w : workers) w.join();
    }
    template <class F>
    auto submit(F f) -> std::future<decltype(f())> {
        using R = decltype(f());
        auto task = std::make_shared<std::packaged_task<R()>>(std::move(f));
        std::future<R> fut = task->get_future();
        { std::unique_lock<std::mutex> lk(m); tasks.emplace([task] { (*task)(); }); }
        cv.notify_one();
        return fut;
    }
private:
    void worker_loop() {
        for (;;) {
            std::function<void()> job;
            {
                std::unique_lock<std::mutex> lk(m);
                cv.wait(lk, [this] { return stopping || !tasks.empty(); });
                if (stopping && tasks.empty()) return;
                job = std::move(tasks.front());
                tasks.pop();
            }
            job();
        }
    }
    std::vector<std::thread> workers;
    std::queue<std::function<void()>> tasks;
    std::mutex m;
    std::condition_variable cv;
    bool stopping = false;
};

// ---------------------------------------------------------------------------
// Deterministic Miller-Rabin primality test
//
// Witnesses {2,3,5,7,11,13,17,19,23,29,31,37} cover all n < 3.317e24,
// which includes every 64-bit integer.  No false positives.
// ---------------------------------------------------------------------------
static uint64_t mulmod64(uint64_t a, uint64_t b, uint64_t m) {
#if defined(__GNUC__) || defined(__clang__)
    return static_cast<uint64_t>(
        static_cast<unsigned __int128>(a) * b % m);
#else
    // Portable fallback: binary (Russian-peasant) multiplication, O(log b).
    // Uses overflow-safe conditional addition/doubling: instead of computing
    // x+y and then subtracting m, we test x >= m-y (equivalent, no overflow).
    uint64_t res = 0;
    a %= m;
    while (b) {
        if (b & 1) { if (res >= m - a) res -= m - a; else res += a; }
        if (a >= m - a) a -= m - a; else a += a;
        b >>= 1;
    }
    return res;
#endif
}

static uint64_t powmod64(uint64_t base, uint64_t exp, uint64_t mod) {
    uint64_t result = 1;
    base %= mod;
    while (exp) {
        if (exp & 1) result = mulmod64(result, base, mod);
        base = mulmod64(base, base, mod);
        exp >>= 1;
    }
    return result;
}

static bool mr_witness(uint64_t n, uint64_t d, int r, uint64_t a) {
    uint64_t x = powmod64(a, d, n);
    if (x == 1 || x == n - 1) return true;
    for (int i = 0; i < r - 1; ++i) {
        x = mulmod64(x, x, n);
        if (x == n - 1) return true;
    }
    return false;
}

static bool is_prime_mr(uint64_t n) {
    if (n < 2)  return false;
    if (n == 2 || n == 3 || n == 5) return true;
    if (!(n & 1) || n % 3 == 0 || n % 5 == 0) return false;
    uint64_t d = n - 1; int r = 0;
    while (!(d & 1)) { d >>= 1; ++r; }
    for (uint64_t a : {2ull,3ull,5ull,7ull,11ull,13ull,17ull,19ull,23ull,29ull,31ull,37ull}) {
        if (a >= n) continue;
        if (!mr_witness(n, d, r, a)) return false;
    }
    return true;
}

// ---------------------------------------------------------------------------
// Build g_small_primes — Eratosthenes sieve over odd numbers up to
// SMALL_PRIME_LIMIT.  Called once from main() before threads start.
// ---------------------------------------------------------------------------
static void build_small_primes() {
    const std::size_t size = (SMALL_PRIME_LIMIT - 1) / 2; // slots for 3,5,7,...
    std::vector<uint8_t> sieve(size, 0);
    for (std::size_t i = 0; ; ++i) {
        uint64_t p = 2 * i + 3;
        if (p * p > SMALL_PRIME_LIMIT) break;
        if (!sieve[i])
            for (uint64_t j = (p * p - 3) / 2; j < size; j += p)
                sieve[j] = 1;
    }
    g_small_primes.reserve(120'000);
    g_small_primes.push_back(2);
    for (std::size_t i = 0; i < size; ++i)
        if (!sieve[i])
            g_small_primes.push_back(static_cast<uint32_t>(2 * i + 3));
}

// ---------------------------------------------------------------------------
// Timestamp — returns current local time as "YYYY-MM-DD HH:MM:SS".
// ---------------------------------------------------------------------------
static std::string current_timestamp() {
    std::time_t t = std::time(nullptr);
    std::tm tm{};
#ifdef _WIN32
    localtime_s(&tm, &t);
#else
    localtime_r(&t, &tm);
#endif
    char buf[20];
    std::strftime(buf, sizeof(buf), "%Y-%m-%d %H:%M:%S", &tm);
    return std::string(buf);
}

// ---------------------------------------------------------------------------
// Checkpoint writer — opens checkpoint.txt fresh each call (truncating it)
// and writes the current statistics.  Reads only atomics; needs no lock.
// Called from the coordinator thread only.
// ---------------------------------------------------------------------------
static void write_checkpoint() {
    std::ofstream cp("checkpoint.txt"); // default mode = out|trunc → overwrites
    if (!cp.is_open()) return;
    cp << "Goldbach verified up to: "                         << g_checked.load(std::memory_order_relaxed)              << "\n\n"
       << "Goldbach failures found: "                         << g_violation_count.load(std::memory_order_relaxed)      << "\n\n"
       << "Times the emergency search was needed: "           << g_fallback_activations.load(std::memory_order_relaxed) << "\n\n"
       << "Largest number that needed the emergency search: " << g_largest_fallback_N.load(std::memory_order_relaxed)   << "\n\n"
       << "Most work ever needed during an emergency search: "<< g_max_fallback_depth.load(std::memory_order_relaxed)   << " checks\n\n"
       << "Number that was most difficult to verify: "        << g_max_fast_depth_N.load(std::memory_order_relaxed)     << "\n\n"
       << "Most difficult number checked so far: "            << g_max_fast_depth.load(std::memory_order_relaxed)       << " checks\n\n"
       << "Timestamp: " << current_timestamp() << "\n";
    cp.flush();
}

// ---------------------------------------------------------------------------
// Goldbach batch checker
//
// Phase 1 (fast path): iterates g_small_primes as candidate p values and
// tests q = N-p with Miller-Rabin.  Almost always terminates within the first
// one to three iterations.
//
// Phase 2 (completeness fallback): if Phase 1 finds no pair, scans odd
// integers beyond SMALL_PRIME_LIMIT up to N/2, testing both p and q = N-p
// with Miller-Rabin.  This makes correctness unconditional — no unproven
// assumption about small-prime Goldbach coverage is required.
// ---------------------------------------------------------------------------
static std::vector<std::string> check_goldbach_batch(uint64_t even_start,
                                                     uint64_t even_end) {
    std::vector<std::string> results;
    results.reserve(static_cast<std::size_t>((even_end - even_start) / 2));

    // Precompute the fallback start once per batch call.
    const uint64_t fallback_start =
        g_small_primes.empty() ? 3ULL
                               : static_cast<uint64_t>(g_small_primes.back()) + 2;

    for (uint64_t N = even_start; N < even_end; N += 2) {
        bool found = false;
        const uint64_t half = N >> 1;

        // Phase 1: small-prime candidates (fast).
        // fast_depth counts how many primes from g_small_primes were tried
        // (1-indexed; only primes that satisfy p <= N/2 are counted).
        uint64_t fast_depth = 0;
        for (uint32_t p32 : g_small_primes) {
            const uint64_t p = p32;
            if (p > half) break;
            ++fast_depth;
            const uint64_t q = N - p;
            if (is_prime_mr(q)) {
                results.push_back(std::to_string(N) + " = " +
                                  std::to_string(p) + " + " + std::to_string(q));
                found = true;
                // Lock-free CAS: update the fast-path depth record if this is deeper.
                // Exactly one thread wins per new record; that thread writes to the file.
                uint64_t prev = g_max_fast_depth.load(std::memory_order_relaxed);
                while (fast_depth > prev) {
                    if (g_max_fast_depth.compare_exchange_weak(
                            prev, fast_depth,
                            std::memory_order_relaxed,
                            std::memory_order_relaxed)) {
                        g_max_fast_depth_N.store(N, std::memory_order_relaxed);
                        std::lock_guard<std::mutex> lk(g_interesting_mtx);
                        g_interesting_file << "NEW MOST DIFFICULT NUMBER FOUND\n\n"
                                           << "Number=" << N << "\n\n"
                                           << "Checks needed before finding a Goldbach pair=" << fast_depth << "\n\n"
                                           << "Timestamp=" << current_timestamp() << "\n\n";
                        g_interesting_file.flush();
                        break;
                    }
                }
                break;
            }
        }

        // Phase 2: exhaustive fallback beyond SMALL_PRIME_LIMIT.
        // Entered only when every Goldbach pair for this N has both primes
        // above SMALL_PRIME_LIMIT.  No such N is known to exist for uint64_t
        // values, so this path is never expected to be taken in practice.
        // fallback_depth counts each p += 2 step (includes composite p values).
        if (!found && fallback_start <= half) {
            g_fallback_activations.fetch_add(1, std::memory_order_relaxed);
            uint64_t fallback_depth = 0;
            for (uint64_t p = fallback_start; p <= half; p += 2) {
                ++fallback_depth;
                if (is_prime_mr(p)) {
                    const uint64_t q = N - p;
                    if (is_prime_mr(q)) {
                        results.push_back(std::to_string(N) + " = " +
                                          std::to_string(p) + " + " +
                                          std::to_string(q));
                        found = true;
                        // Lock-free CAS: update the fallback depth record if deeper.
                        uint64_t prev = g_max_fallback_depth.load(std::memory_order_relaxed);
                        while (fallback_depth > prev) {
                            if (g_max_fallback_depth.compare_exchange_weak(
                                    prev, fallback_depth,
                                    std::memory_order_relaxed,
                                    std::memory_order_relaxed)) {
                                g_largest_fallback_N.store(N, std::memory_order_relaxed);
                                std::lock_guard<std::mutex> lk(g_interesting_mtx);
                                g_interesting_file << "NEW EMERGENCY SEARCH RECORD\n\n"
                                                   << "Number=" << N << "\n\n"
                                                   << "Checks needed before finding a Goldbach pair=" << fallback_depth << "\n\n"
                                                   << "Timestamp=" << current_timestamp() << "\n\n";
                                g_interesting_file.flush();
                                break;
                            }
                        }
                        break;
                    }
                }
            }
        }

        if (!found)
            results.push_back("VIOLATION: " + std::to_string(N) +
                               " has no prime pair!");
    }
    return results;
}

// ---------------------------------------------------------------------------
// Goldbach coordinator
//
// Distributes batches of even numbers to worker threads, collects results,
// and appends them to goldbach.txt.  No longer gated on the prime-enumerator
// thread: verification is self-contained via Miller-Rabin.
// ---------------------------------------------------------------------------
static void goldbach_coordinator() {
    uint64_t next_even = 4;

    // Open all output files before spawning worker threads so that workers
    // can write to g_interesting_file immediately on their first batch.
    std::ofstream f("goldbach.txt", std::ios::app);
    if (!f.is_open()) {
        std::lock_guard<std::mutex> lk(g_io_mtx);
        std::cerr << "[Goldbach] ERROR: cannot open goldbach.txt for writing.\n";
        g_stop.store(true);
        return;
    }
    {
        // Open violations.txt under the violations mutex so any future thread
        // that also holds g_violations_mtx before writing is guaranteed safe.
        std::lock_guard<std::mutex> lk(g_violations_mtx);
        g_viol_file.open("violations.txt", std::ios::app);
    }
    if (!g_viol_file.is_open()) {
        std::lock_guard<std::mutex> lk(g_io_mtx);
        std::cerr << "[Goldbach] ERROR: cannot open violations.txt for writing.\n";
        g_stop.store(true);
        return;
    }
    {
        std::lock_guard<std::mutex> lk(g_interesting_mtx);
        g_interesting_file.open("interesting_cases.txt", std::ios::app);
    }
    if (!g_interesting_file.is_open()) {
        std::lock_guard<std::mutex> lk(g_io_mtx);
        std::cerr << "[Goldbach] ERROR: cannot open interesting_cases.txt for writing.\n";
        g_stop.store(true);
        return;
    }

    ThreadPool pool(g_num_workers); // workers start here; all files are already open
    std::deque<std::pair<std::future<std::vector<std::string>>, uint64_t>> queue;
    std::vector<std::string> write_buf;
    write_buf.reserve(WRITE_BATCH);
    uint64_t last_checkpoint_at = 0;

    auto flush_write_buf = [&] {
        for (auto &s : write_buf) f << s << '\n';
        f.flush();
        write_buf.clear();
    };

    while (!g_stop.load()) {
        // Keep the pipeline full: at most num_workers*2 batches in flight
        while (queue.size() < static_cast<std::size_t>(g_num_workers) * 2) {
            // Guard against uint64_t wrap-around near UINT64_MAX.
            if (next_even > UINT64_MAX - BATCH_SIZE * 2) {
                g_stop.store(true);
                break;
            }
            const uint64_t batch_end = next_even + BATCH_SIZE * 2;
            const uint64_t es = next_even, ee = batch_end;
            queue.emplace_back(
                pool.submit([es, ee] { return check_goldbach_batch(es, ee); }),
                batch_end - 2);
            next_even = batch_end;
        }

        if (queue.front().first.wait_for(std::chrono::milliseconds(1)) ==
            std::future_status::ready) {
            auto item = std::move(queue.front());
            queue.pop_front();
            auto lines = item.first.get();
            for (auto &line : lines) {
                if (line.rfind("VIOLATION", 0) == 0) {
                    { std::lock_guard<std::mutex> lk(g_violations_mtx);
                      g_violations.push_back(line);
                      g_viol_file << line << '\n';
                      g_viol_file.flush(); }
                    g_violation_count.fetch_add(1, std::memory_order_relaxed);
                    std::lock_guard<std::mutex> lk(g_io_mtx);
                    std::cout << "\n*** " << line << " ***\n> " << std::flush;
                } else {
                    write_buf.push_back(line);
                }
            }
            if (write_buf.size() >= WRITE_BATCH) flush_write_buf();
            g_checked.store(item.second);
            if (item.second - last_checkpoint_at >= CHECKPOINT_INTERVAL) {
                write_checkpoint();
                last_checkpoint_at = item.second;
            }
        }
    }

    // Drain any in-flight work
    for (auto &qi : queue) {
        auto lines = qi.first.get();
        for (auto &line : lines) {
            if (line.rfind("VIOLATION", 0) == 0) {
                std::lock_guard<std::mutex> lk(g_violations_mtx);
                g_violations.push_back(line);
                g_viol_file << line << '\n';
                g_viol_file.flush();
                g_violation_count.fetch_add(1, std::memory_order_relaxed);
            } else {
                write_buf.push_back(line);
            }
        }
        g_checked.store(qi.second);
    }
    flush_write_buf();
    write_checkpoint(); // final checkpoint so the last state is always on disk

    std::lock_guard<std::mutex> lk(g_io_mtx);
    std::cout << "\n[Goldbach] Verified up to " << g_checked.load()
              << ". Violations: " << g_violations.size() << ".\n";
}

// ---------------------------------------------------------------------------
// Prime enumerator (display only — does not feed the Goldbach verifier)
//
// Runs a segmented sieve beyond SMALL_PRIME_LIMIT using g_small_primes as
// the base.  Updates g_total_primes and g_prime_frontier for the status
// command.  The segment buffer (~2 MB) is reused each iteration — memory
// usage here is constant.
//
// Correctness limit: the sieve base covers primes up to SMALL_PRIME_LIMIT,
// which is sufficient for segments whose high end is <= SMALL_PRIME_LIMIT^2
// ≈ 2.25e12.  Beyond that, composites whose smallest prime factor exceeds
// SMALL_PRIME_LIMIT are never crossed off and are counted as primes, so
// g_total_primes becomes over-counted.  Goldbach verification is unaffected.
// ---------------------------------------------------------------------------
static void enumerate_primes_forever() {
    g_total_primes.store(static_cast<uint64_t>(g_small_primes.size()));
    g_prime_frontier.store(g_small_primes.empty() ? 2 : g_small_primes.back());

    uint64_t seg_lo = SMALL_PRIME_LIMIT + 2;
    if (seg_lo % 2 == 0) ++seg_lo; // ensure odd start

    std::vector<uint8_t> seg_buf(SEG_SIZE, 0); // reused each segment

    while (!g_stop.load()) {
        const uint64_t seg_hi = seg_lo + 2 * SEG_SIZE - 2;
        const uint64_t sqrt_hi =
            static_cast<uint64_t>(std::sqrt(static_cast<double>(seg_hi))) + 2;

        seg_buf.assign(SEG_SIZE, 0);

        for (uint32_t p32 : g_small_primes) {
            if (p32 == 2) continue;
            const uint64_t p = p32;
            if (p > sqrt_hi) break;
            uint64_t start = ((seg_lo + p - 1) / p) * p;
            if (start % 2 == 0) start += p;
            if (start == p)     start += 2 * p; // don't mark p itself
            if (start > seg_hi) continue;
            const uint64_t idx = (start - seg_lo) / 2;
            for (uint64_t j = idx; j < SEG_SIZE; j += p)
                seg_buf[j] = 1;
        }

        uint64_t found = 0, last_p = 0;
        for (uint64_t i = 0; i < SEG_SIZE; ++i) {
            if (!seg_buf[i]) {
                ++found;
                last_p = seg_lo + 2 * i;
            }
        }
        if (found > 0) {
            g_total_primes.fetch_add(found);
            g_prime_frontier.store(last_p);
        } else {
            g_prime_frontier.store(seg_hi);
        }

        // Guard against uint64_t wrap-around
        if (seg_hi > UINT64_MAX - 2 * SEG_SIZE) break;
        seg_lo = seg_hi + 2;
    }
}

// ---------------------------------------------------------------------------
// Utilities
// ---------------------------------------------------------------------------
static std::string strip_lower(const std::string &s) {
    std::size_t a = 0, b = s.size();
    while (a < b && std::isspace(static_cast<unsigned char>(s[a])))     ++a;
    while (b > a && std::isspace(static_cast<unsigned char>(s[b - 1]))) --b;
    std::string r = s.substr(a, b - a);
    std::transform(r.begin(), r.end(), r.begin(),
                   [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
    return r;
}

// ---------------------------------------------------------------------------
// main
// ---------------------------------------------------------------------------
int main() {
    unsigned cpu = std::thread::hardware_concurrency();
    if (cpu == 0) cpu = 1;
    g_num_workers = std::max(1u, cpu - 1);

    std::cout << "Is every even integer > 2 the sum of two primes?\n";
    std::cout << "Using " << g_num_workers
              << " worker thread(s) for Goldbach verification.\n";
    std::cout << "Commands: status | stop | quit\n\n";
    std::cout << "Building prime table (primes up to "
              << SMALL_PRIME_LIMIT << ")..." << std::flush;

    build_small_primes();
    std::cout << " done. (" << g_small_primes.size() << " primes)\n\n";

    std::thread prime_thread(enumerate_primes_forever);
    std::thread goldbach_thread(goldbach_coordinator);
    std::cout << "Running.\n\n";

    std::string line;
    while (true) {
        std::cout << "> " << std::flush;
        if (!std::getline(std::cin, line)) break;
        const std::string cmd = strip_lower(line);
        if (cmd == "status") {
            const uint64_t tp   = g_total_primes.load();
            const uint64_t pf   = g_prime_frontier.load();
            const uint64_t chk  = g_checked.load();
            const uint64_t fa   = g_fallback_activations.load();
            const uint64_t lfn  = g_largest_fallback_N.load();
            const uint64_t mfd  = g_max_fallback_depth.load();
            const uint64_t mfsd = g_max_fast_depth.load();
            const uint64_t mfsn = g_max_fast_depth_N.load();
            std::vector<std::string> vio;
            { std::lock_guard<std::mutex> lk(g_violations_mtx); vio = g_violations; }
            std::lock_guard<std::mutex> lk(g_io_mtx);
            std::cout << "Primes enumerated       : " << tp
                      << "  (frontier: " << pf << ")\n";
            std::cout << "Goldbach verified       : up to " << chk << "\n";
            std::cout << "Fallback activations    : " << fa  << "\n";
            std::cout << "Largest fallback N      : " << lfn << "\n";
            std::cout << "Deepest fallback depth  : " << mfd << "\n";
            std::cout << "Largest fast-path depth : " << mfsd << "\n";
            std::cout << "Largest fast-path N     : " << mfsn << "\n";
            if (!vio.empty()) {
                std::cout << "VIOLATIONS (" << vio.size() << "):\n";
                for (auto &v : vio) std::cout << "  " << v << "\n";
            } else {
                std::cout << "No violations found so far.\n";
            }
        } else if (cmd == "stop") {
            g_stop.store(true);
            break;
        } else if (cmd == "quit") {
            { std::lock_guard<std::mutex> lk(g_io_mtx);
              std::cout << "Force quitting.\n"; }
            std::_Exit(0);
        } else if (!cmd.empty()) {
            std::cout << "Commands: status | stop | quit\n";
        }
    }

    g_stop.store(true);
    if (prime_thread.joinable())    prime_thread.join();
    if (goldbach_thread.joinable()) goldbach_thread.join();
    return 0;
}
     
