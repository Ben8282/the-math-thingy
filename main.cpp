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

constexpr uint64_t BATCH_SIZE        = 10000;
constexpr std::size_t WRITE_BATCH    = 1000;
constexpr uint64_t SEGMENT_SIZE      = 1ull << 21;
constexpr uint64_t SMALL_PRIME_LIMIT = 1000000;
constexpr uint64_t SIEVE_LIMIT       = 100000000;
constexpr std::size_t MAX_PRIMES     = 10000000;

static std::vector<uint8_t>  g_sieve;
static std::vector<uint32_t> g_primes;
static std::atomic<std::size_t> g_prime_count{1};
static std::atomic<uint64_t> g_total_primes{1};
static std::atomic<uint64_t> g_current{3};
static std::atomic<uint64_t> g_checked{2};
static std::atomic<bool>     g_stop{false};
static std::vector<std::string> g_violations;
static std::mutex g_violations_mtx;
static std::mutex g_io_mtx;
static unsigned g_num_workers = 1;

class ThreadPool {
public:
    explicit ThreadPool(std::size_t n) {
        for (std::size_t i = 0; i < n; ++i)
            workers.emplace_back([this] { worker_loop(); });
    }
    ~ThreadPool() {
        {
            std::unique_lock<std::mutex> lk(m);
            stopping = true;
        }
        cv.notify_all();
        for (auto &w : workers) w.join();
    }
    template <class F>
    auto submit(F f) -> std::future<decltype(f())> {
        using R = decltype(f());
        auto task = std::make_shared<std::packaged_task<R()>>(std::move(f));
        std::future<R> fut = task->get_future();
        {
            std::unique_lock<std::mutex> lk(m);
            tasks.emplace([task] { (*task)(); });
        }
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

static bool is_prime(uint64_t n) {
    if (n < 2) return false;
    if (n == 2) return true;
    if (n % 2 == 0) return false;
    for (uint64_t i = 3; i * i <= n; i += 2)
        if (n % i == 0) return false;
    return true;
}

static std::vector<uint8_t> odd_sieve(uint64_t limit) {
    std::size_t size = (limit - 1) / 2;
    std::vector<uint8_t> sieve(size, 0);
    uint64_t i = 0;
    for (;;) {
        uint64_t p = 2 * i + 3;
        if (p * p > limit) break;
        if (!sieve[i]) {
            uint64_t start = (p * p - 3) / 2;
            for (uint64_t j = start; j < size; j += p) sieve[j] = 1;
        }
        ++i;
    }
    return sieve;
}

static std::vector<uint64_t> segment_sieve(uint64_t seg_lo, uint64_t seg_hi,
                                           const std::vector<uint64_t> &small_primes) {
    std::size_t size = static_cast<std::size_t>((seg_hi - seg_lo) / 2 + 1);
    std::vector<uint8_t> sieve(size, 0);
    for (uint64_t p : small_primes) {
        if (p == 2) continue;
        uint64_t start = ((seg_lo + p - 1) / p) * p;
        if (start % 2 == 0) start += p;
        if (start == p) start += 2 * p;
        if (start > seg_hi) continue;
        uint64_t start_idx = (start - seg_lo) / 2;
        for (uint64_t j = start_idx; j < size; j += p) sieve[j] = 1;
    }
    std::vector<uint64_t> out;
    for (std::size_t i = 0; i < size; ++i)
        if (!sieve[i]) out.push_back(seg_lo + 2 * i);
    return out;
}

static std::vector<std::string> check_goldbach_batch(uint64_t even_start, uint64_t even_end,
                                                     std::size_t n_primes) {
    const uint32_t *p_buf = g_primes.data();
    const uint8_t  *s_buf = g_sieve.data();
    const uint64_t sieve_slots = g_sieve.size();
    std::vector<std::string> results;
    for (uint64_t even = even_start; even < even_end; even += 2) {
        bool found = false;
        uint64_t half = even >> 1;
        for (std::size_t i = 0; i < n_primes; ++i) {
            uint64_t p = p_buf[i];
            if (p > half) break;
            uint64_t q = even - p;
            bool is_q_prime;
            if (q == 2) {
                is_q_prime = true;
            } else if (q < 3 || !(q & 1)) {
                is_q_prime = false;
            } else {
                uint64_t q_idx = (q - 3) >> 1;
                is_q_prime = (q_idx < sieve_slots) ? (s_buf[q_idx] == 0) : is_prime(q);
            }
            if (is_q_prime) {
                results.push_back(std::to_string(even) + " = " + std::to_string(p) +
                                  " + " + std::to_string(q));
                found = true;
                break;
            }
        }
        if (!found)
            results.push_back("VIOLATION: " + std::to_string(even) + " has no prime pair!");
    }
    return results;
}

static void generate_primes_forever() {
    std::size_t idx = g_prime_count.load();
    std::vector<uint64_t> small_primes;
    std::ofstream f("primes.txt", std::ios::app);
    std::vector<std::string> write_buf;
    write_buf.reserve(WRITE_BATCH);

    auto flush_buf = [&] {
        for (auto &s : write_buf) f << s;
        f.flush();
        g_prime_count.store(idx);
        write_buf.clear();
    };

    const std::size_t sieve_size = g_sieve.size();
    for (std::size_t slot_idx = 0; slot_idx < sieve_size; ++slot_idx) {
        if (g_stop.load()) break;
        uint64_t n = 2ull * slot_idx + 3;
        g_current.store(n);
        if (g_sieve[slot_idx] == 0) {
            g_total_primes.fetch_add(1);
            if (n <= SMALL_PRIME_LIMIT) small_primes.push_back(n);
            if (idx < MAX_PRIMES) g_primes[idx++] = static_cast<uint32_t>(n);
            write_buf.push_back(std::to_string(n) + "\n");
            if (write_buf.size() >= WRITE_BATCH) flush_buf();
        }
    }
    if (!write_buf.empty()) flush_buf();

    if (!g_stop.load()) {
        uint64_t seg_lo = SIEVE_LIMIT + 1;
        if (seg_lo % 2 == 0) ++seg_lo;

        while (!g_stop.load()) {
            uint64_t seg_hi = seg_lo + SEGMENT_SIZE * 2 - 2;
            uint64_t sqrt_hi = static_cast<uint64_t>(std::sqrt(static_cast<double>(seg_hi))) + 1;
            std::vector<uint64_t> seg_small;
            for (uint64_t p : small_primes)
                if (p <= sqrt_hi) seg_small.push_back(p);

            std::vector<uint64_t> seg_primes = segment_sieve(seg_lo, seg_hi, seg_small);

            for (uint64_t p : seg_primes) {
                if (g_stop.load()) break;
                g_current.store(p);
                g_total_primes.fetch_add(1);
                if (idx < MAX_PRIMES) g_primes[idx++] = static_cast<uint32_t>(p);
                write_buf.push_back(std::to_string(p) + "\n");
                if (write_buf.size() >= WRITE_BATCH) flush_buf();
            }
            if (seg_primes.empty()) g_current.store(seg_hi);
            seg_lo = seg_hi + 2;
        }
    }
    if (!write_buf.empty()) flush_buf();

    {
        std::lock_guard<std::mutex> lk(g_io_mtx);
        std::cout << "\n[Primes] Found " << g_total_primes.load()
                  << " primes up to " << g_current.load() << ".\n";
    }
}

static void goldbach_coordinator() {
    uint64_t next_even = 4;
    ThreadPool pool(g_num_workers);
    std::ofstream f("goldbach.txt", std::ios::app);
    std::deque<std::pair<std::future<std::vector<std::string>>, uint64_t>> queue;

    while (!g_stop.load()) {
        uint64_t batch_end = next_even + BATCH_SIZE * 2;
        while (queue.size() < static_cast<std::size_t>(g_num_workers) * 2 &&
               g_current.load() > batch_end) {
            std::size_t n_p = g_prime_count.load();
            uint64_t es = next_even, ee = batch_end;
            auto fut = pool.submit([es, ee, n_p] { return check_goldbach_batch(es, ee, n_p); });
            queue.emplace_back(std::move(fut), batch_end - 2);
            next_even = batch_end;
            batch_end = next_even + BATCH_SIZE * 2;
        }

        if (!queue.empty() &&
            queue.front().first.wait_for(std::chrono::seconds(0)) == std::future_status::ready) {
            auto item = std::move(queue.front());
            queue.pop_front();
            auto lines = item.first.get();
            for (auto &line : lines) {
                f << line << "\n";
                if (line.rfind("VIOLATION", 0) == 0) {
                    {
                        std::lock_guard<std::mutex> lk(g_violations_mtx);
                        g_violations.push_back(line);
                    }
                    std::lock_guard<std::mutex> lk(g_io_mtx);
                    std::cout << "\n*** " << line << " ***\n> " << std::flush;
                }
            }
            f.flush();
            g_checked.store(item.second);
        } else {
            std::this_thread::sleep_for(std::chrono::microseconds(500));
        }
    }

    for (auto &qi : queue) {
        auto lines = qi.first.get();
        for (auto &line : lines) {
            f << line << "\n";
            if (line.rfind("VIOLATION", 0) == 0) {
                std::lock_guard<std::mutex> lk(g_violations_mtx);
                g_violations.push_back(line);
            }
        }
        f.flush();
        g_checked.store(qi.second);
    }

    {
        std::lock_guard<std::mutex> lk(g_io_mtx);
        std::cout << "\n[Goldbach] Verified up to " << g_checked.load()
                  << ". Violations: " << g_violations.size() << ".\n";
    }
}

static std::string strip_lower(const std::string &s) {
    std::size_t a = 0, b = s.size();
    while (a < b && std::isspace(static_cast<unsigned char>(s[a]))) ++a;
    while (b > a && std::isspace(static_cast<unsigned char>(s[b - 1]))) --b;
    std::string r = s.substr(a, b - a);
    std::transform(r.begin(), r.end(), r.begin(),
                   [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
    return r;
}

int main() {
    unsigned cpu = std::thread::hardware_concurrency();
    if (cpu == 0) cpu = 1;
    g_num_workers = std::max(1u, cpu - 1);

    std::cout << "is it true that all even numbers greater than 2 are a sum of 2 prime numbers\n";
    std::cout << "Using " << g_num_workers << " worker threads for Goldbach verification.\n";
    std::cout << "Type 'status' to check progress, 'stop' to stop, or 'quit' to force quit.\n";
    std::cout << "Computing sieve and initialising buffers..." << std::flush;

    g_sieve = odd_sieve(SIEVE_LIMIT);
    g_primes.assign(MAX_PRIMES, 0);
    g_primes[0] = 2;
    g_prime_count.store(1);
    g_total_primes.store(1);
    std::cout << " done.\n\n";

    std::thread prime_thread(generate_primes_forever);
    std::thread goldbach_thread(goldbach_coordinator);
    std::cout << "Prime generation and Goldbach verification started.\n\n";

    std::string line;
    while (true) {
        std::cout << "> " << std::flush;
        if (!std::getline(std::cin, line)) break;
        std::string cmd = strip_lower(line);
        if (cmd == "status") {
            uint64_t tp = g_total_primes.load();
            uint64_t cur = g_current.load();
            uint64_t chk = g_checked.load();
            std::vector<std::string> vio;
            {
                std::lock_guard<std::mutex> lk(g_violations_mtx);
                vio = g_violations;
            }
            std::lock_guard<std::mutex> lk(g_io_mtx);
            std::cout << "Primes: " << tp << " found, checking up to " << cur << ".\n";
            std::cout << "Goldbach: verified up to " << chk << ".\n";
            if (!vio.empty()) {
                std::cout << "VIOLATIONS: " << vio.size() << "\n";
                for (auto &v : vio) std::cout << "  " << v << "\n";
            } else {
                std::cout << "No violations found so far.\n";
            }
        } else if (cmd == "stop") {
            g_stop.store(true);
            break;
        } else if (cmd == "quit") {
            {
                std::lock_guard<std::mutex> lk(g_io_mtx);
                std::cout << "Force quitting...\n";
            }
            std::_Exit(0);
        } else if (!cmd.empty()) {
            std::cout << "Commands: status | stop | quit\n";
        }
    }

    g_stop.store(true);
    if (prime_thread.joinable()) prime_thread.join();
    if (goldbach_thread.joinable()) goldbach_thread.join();
    return 0;
}
