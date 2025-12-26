# High-Performance Concurrent Runtime Stack - Part 2: Runtime Implementation

**Part of:** [High-Performance Concurrent Runtime Stack](high_performance_concurrent_runtime.md)

---

## Complete Runtime Implementation

### include/runtime/allocator.hpp

```cpp
#pragma once

#include <mimalloc.h>
#include <cstddef>
#include <memory>

namespace rt {

//==============================================================================
// mimalloc STL Allocator
//==============================================================================
template<typename T>
struct MiAllocator {
    using value_type = T;
    using size_type = std::size_t;
    using difference_type = std::ptrdiff_t;
    using propagate_on_container_move_assignment = std::true_type;
    using is_always_equal = std::true_type;

    MiAllocator() noexcept = default;
    template<typename U> MiAllocator(const MiAllocator<U>&) noexcept {}

    T* allocate(size_type n) {
        if (n > std::size_t(-1) / sizeof(T)) throw std::bad_alloc();
        if (auto p = static_cast<T*>(mi_malloc(n * sizeof(T)))) return p;
        throw std::bad_alloc();
    }

    void deallocate(T* p, size_type) noexcept {
        mi_free(p);
    }

    template<typename U>
    bool operator==(const MiAllocator<U>&) const noexcept { return true; }
    
    template<typename U>
    bool operator!=(const MiAllocator<U>&) const noexcept { return false; }
};

// Convenient aliases
template<typename T>
using MiVector = std::vector<T, MiAllocator<T>>;

template<typename T>
using MiString = std::basic_string<char, std::char_traits<char>, MiAllocator<char>>;

template<typename K, typename V>
using MiUnorderedMap = std::unordered_map<
    K, V, std::hash<K>, std::equal_to<K>,
    MiAllocator<std::pair<const K, V>>
>;

//==============================================================================
// Aligned allocation for cache-line padding
//==============================================================================
template<typename T, size_t Alignment = 64>
struct AlignedMiAllocator {
    using value_type = T;

    T* allocate(size_t n) {
        return static_cast<T*>(mi_malloc_aligned(n * sizeof(T), Alignment));
    }

    void deallocate(T* p, size_t) {
        mi_free(p);
    }
};

} // namespace rt
```

### include/runtime/queue.hpp

```cpp
#pragma once

#include <concurrentqueue.h>
#include <mimalloc.h>
#include <cstddef>
#include <optional>

namespace rt {

//==============================================================================
// Lock-Free Queue (moodycamel + mimalloc)
//==============================================================================
template<typename T>
class LockFreeQueue {
public:
    // Custom traits to use mimalloc
    struct MiTraits : moodycamel::ConcurrentQueueDefaultTraits {
        static void* malloc(size_t size) { return mi_malloc(size); }
        static void free(void* ptr) { mi_free(ptr); }
    };

private:
    moodycamel::ConcurrentQueue<T, MiTraits> queue_;

public:
    explicit LockFreeQueue(size_t initial_capacity = 1024)
        : queue_(initial_capacity) {}

    //=== Single Operations ===
    
    void push(const T& item) {
        queue_.enqueue(item);
    }

    void push(T&& item) {
        queue_.enqueue(std::move(item));
    }

    bool try_pop(T& item) {
        return queue_.try_dequeue(item);
    }

    std::optional<T> try_pop() {
        T item;
        if (queue_.try_dequeue(item)) {
            return item;
        }
        return std::nullopt;
    }

    //=== Bulk Operations (10-100x faster) ===
    
    template<typename Iterator>
    void push_bulk(Iterator begin, size_t count) {
        queue_.enqueue_bulk(begin, count);
    }

    template<typename Iterator>
    size_t try_pop_bulk(Iterator out, size_t max_count) {
        return queue_.try_dequeue_bulk(out, max_count);
    }

    //=== Producer Token (reduces contention) ===
    
    using ProducerToken = moodycamel::ProducerToken;
    
    ProducerToken make_producer_token() {
        return ProducerToken(queue_);
    }

    void push(ProducerToken& token, const T& item) {
        queue_.enqueue(token, item);
    }

    void push(ProducerToken& token, T&& item) {
        queue_.enqueue(token, std::move(item));
    }

    //=== Utilities ===
    
    size_t size_approx() const {
        return queue_.size_approx();
    }

    bool empty() const {
        return queue_.size_approx() == 0;
    }
};

//==============================================================================
// SPSC Queue (Single-Producer Single-Consumer, even faster)
//==============================================================================
template<typename T>
class SPSCQueue {
    moodycamel::ReaderWriterQueue<T> queue_;

public:
    explicit SPSCQueue(size_t capacity = 1024) : queue_(capacity) {}

    void push(const T& item) { queue_.enqueue(item); }
    void push(T&& item) { queue_.enqueue(std::move(item)); }
    bool try_pop(T& item) { return queue_.try_dequeue(item); }
    size_t size_approx() const { return queue_.size_approx(); }
};

} // namespace rt
```

### include/runtime/hashmap.hpp

```cpp
#pragma once

#include <libcuckoo/cuckoohash_map.hh>
#include <cds/init.h>
#include <cds/gc/hp.h>
#include <cds/gc/dhp.h>
#include <cds/container/split_list_map_hp.h>
#include <cds/container/michael_map_hp.h>
#include "allocator.hpp"

#include <optional>
#include <functional>
#include <string>

namespace rt {

//==============================================================================
// Fast HashMap (libcuckoo + mimalloc)
// - NOT lock-free (fine-grained locks)
// - Maximum throughput
// - Best for most use cases
//==============================================================================
template<typename K, typename V,
         typename Hash = std::hash<K>,
         typename Equal = std::equal_to<K>>
class FastHashMap {
    using Alloc = MiAllocator<std::pair<const K, V>>;
    libcuckoo::cuckoohash_map<K, V, Hash, Equal, Alloc> map_;

public:
    explicit FastHashMap(size_t initial_capacity = 1024)
        : map_(initial_capacity) {}

    //=== Basic Operations ===
    
    void insert(const K& key, const V& value) {
        map_.insert(key, value);
    }

    bool insert_or_assign(const K& key, const V& value) {
        return map_.insert_or_assign(key, value);
    }

    bool find(const K& key, V& value) const {
        return map_.find(key, value);
    }

    std::optional<V> get(const K& key) const {
        V value;
        if (map_.find(key, value)) return value;
        return std::nullopt;
    }

    bool contains(const K& key) const {
        return map_.contains(key);
    }

    bool erase(const K& key) {
        return map_.erase(key);
    }

    //=== Atomic Updates ===
    
    template<typename Updater>
    void upsert(const K& key, Updater updater, const V& default_val) {
        map_.upsert(key, std::move(updater), default_val);
    }

    template<typename Fn>
    bool update(const K& key, Fn fn) {
        return map_.update_fn(key, std::move(fn));
    }

    //=== Utilities ===
    
    size_t size() const { return map_.size(); }
    bool empty() const { return map_.empty(); }
    void clear() { map_.clear(); }
    void reserve(size_t n) { map_.reserve(n); }

    // Locked table for iteration
    auto lock_table() { return map_.lock_table(); }
    auto lock_table() const { return map_.lock_table(); }
};

//==============================================================================
// Lock-Free HashMap (libcds + mimalloc)
// - True lock-free with Hazard Pointers
// - Bounded latency
// - Best for real-time, high-contention scenarios
//==============================================================================
template<typename K, typename V,
         typename Hash = std::hash<K>,
         typename Equal = std::equal_to<K>>
class LockFreeHashMap {
    // SplitListMap: lock-free, resizable, good all-around
    struct MapTraits : public cds::container::split_list::traits {
        typedef cds::atomicity::item_counter item_counter;
        typedef Hash hash;
        typedef Equal equal_to;
    };

    using Map = cds::container::SplitListMap<cds::gc::HP, K, V, MapTraits>;
    Map map_;

public:
    explicit LockFreeHashMap(size_t initial_capacity = 1024)
        : map_(initial_capacity) {}

    //=== Basic Operations ===
    
    bool insert(const K& key, const V& value) {
        return map_.insert(key, value);
    }

    bool find(const K& key, V& value) const {
        return map_.find(key, [&value](const auto& item) {
            value = item.second;
        });
    }

    std::optional<V> get(const K& key) const {
        V value;
        if (find(key, value)) return value;
        return std::nullopt;
    }

    bool contains(const K& key) const {
        return map_.contains(key);
    }

    bool erase(const K& key) {
        return map_.erase(key);
    }

    //=== Atomic Updates ===
    
    template<typename Fn>
    bool update(const K& key, Fn fn) {
        return map_.update(key, [&fn](bool exists, auto& item) {
            if (exists) fn(item.second);
            return true;
        });
    }

    bool upsert(const K& key, const V& value) {
        auto result = map_.update(key, [&value](bool, auto& item) {
            item.second = value;
            return true;
        }, std::make_pair(key, value));
        return result.first;
    }

    //=== Utilities ===
    
    size_t size() const { return map_.size(); }
    bool empty() const { return map_.empty(); }
    void clear() { map_.clear(); }
};

//==============================================================================
// Alternative: MichaelHashMap (fixed bucket count, slightly faster)
//==============================================================================
template<typename K, typename V>
class LockFreeHashMapFixed {
    struct MapTraits : public cds::container::michael_map::traits {
        typedef cds::atomicity::item_counter item_counter;
    };

    using Map = cds::container::MichaelHashMap<cds::gc::HP, K, V, MapTraits>;
    Map map_;

public:
    explicit LockFreeHashMapFixed(size_t bucket_count = 1024)
        : map_(bucket_count) {}

    bool insert(const K& key, const V& value) {
        return map_.insert(key, value);
    }

    bool find(const K& key, V& value) const {
        return map_.find(key, [&value](const auto& item) {
            value = item.second;
        });
    }

    bool erase(const K& key) {
        return map_.erase(key);
    }

    size_t size() const { return map_.size(); }
};

} // namespace rt
```

### include/runtime/scheduler.hpp

```cpp
#pragma once

#include <tbb/tbb.h>
#include <tbb/task_arena.h>
#include <tbb/task_group.h>
#include <tbb/parallel_for.h>
#include <tbb/parallel_reduce.h>
#include <tbb/combinable.h>
#include <tbb/flow_graph.h>

#include <functional>
#include <thread>
#include <vector>

namespace rt {

//==============================================================================
// Scheduler (TBB wrapper)
//==============================================================================
class Scheduler {
    tbb::task_arena arena_;

public:
    explicit Scheduler(int num_threads = 0)
        : arena_(num_threads > 0 ? num_threads
                                  : std::thread::hardware_concurrency()) {}

    //=== Parallel For ===
    
    template<typename Fn>
    void parallel_for(size_t n, Fn&& fn) {
        arena_.execute([&] {
            tbb::parallel_for(size_t(0), n, std::forward<Fn>(fn));
        });
    }

    template<typename Fn>
    void parallel_for(size_t begin, size_t end, Fn&& fn) {
        arena_.execute([&] {
            tbb::parallel_for(begin, end, std::forward<Fn>(fn));
        });
    }

    template<typename Range, typename Fn>
    void parallel_for_range(const Range& range, Fn&& fn) {
        arena_.execute([&] {
            tbb::parallel_for(range, std::forward<Fn>(fn));
        });
    }

    //=== Parallel Reduce ===
    
    template<typename T, typename Fn, typename Reduce>
    T parallel_reduce(size_t n, T identity, Fn fn, Reduce reduce) {
        return arena_.execute([&]() -> T {
            return tbb::parallel_reduce(
                tbb::blocked_range<size_t>(0, n),
                identity,
                [&](const auto& r, T local) {
                    for (size_t i = r.begin(); i < r.end(); ++i) {
                        local = fn(local, i);
                    }
                    return local;
                },
                reduce
            );
        });
    }

    //=== Parallel Invoke ===
    
    template<typename... Fns>
    void parallel_invoke(Fns&&... fns) {
        arena_.execute([&] {
            tbb::parallel_invoke(std::forward<Fns>(fns)...);
        });
    }

    //=== Task Group ===
    
    template<typename Fn>
    void async(Fn&& fn) {
        arena_.execute([&] {
            tbb::task_group g;
            g.run(std::forward<Fn>(fn));
            g.wait();
        });
    }

    //=== Properties ===
    
    int concurrency() const { return arena_.max_concurrency(); }
};

//==============================================================================
// Reducer (TBB combinable wrapper)
//==============================================================================
template<typename T, typename ReduceOp = std::plus<T>>
class Reducer {
    tbb::combinable<T> data_;
    ReduceOp reduce_op_;
    T identity_;

public:
    explicit Reducer(T identity = T{}, ReduceOp op = ReduceOp{})
        : data_([identity] { return identity; })
        , reduce_op_(std::move(op))
        , identity_(std::move(identity)) {}

    T& local() { return data_.local(); }
    const T& local() const { return data_.local(); }

    T combine() {
        return data_.combine(reduce_op_);
    }

    template<typename Fn>
    void combine_each(Fn fn) {
        data_.combine_each(std::move(fn));
    }

    void clear() {
        data_.clear();
    }
};

// Common reducer types
template<typename T> using SumReducer = Reducer<T, std::plus<T>>;
template<typename T> using ProductReducer = Reducer<T, std::multiplies<T>>;

template<typename T>
using MinReducer = Reducer<T, decltype([](const T& a, const T& b) { 
    return std::min(a, b); 
})>;

template<typename T>
using MaxReducer = Reducer<T, decltype([](const T& a, const T& b) { 
    return std::max(a, b); 
})>;

} // namespace rt
```

### include/runtime/runtime.hpp

```cpp
#pragma once

// All-in-one include

#include "allocator.hpp"
#include "queue.hpp"
#include "hashmap.hpp"
#include "scheduler.hpp"

#include <mimalloc.h>
#include <cds/init.h>
#include <cds/gc/hp.h>
#include <cds/threading/model.h>

#include <memory>
#include <stdexcept>

namespace rt {

//==============================================================================
// Runtime Configuration
//==============================================================================
struct RuntimeConfig {
    // Threading
    int num_threads = 0;  // 0 = auto-detect
    
    // libcds Hazard Pointer settings
    size_t hp_hazard_ptr_count = 16;
    size_t hp_max_thread_count = 128;
    size_t hp_retired_threshold = 1024;
    
    // mimalloc settings
    bool eager_commit = true;
    bool large_os_pages = false;
    bool show_stats_on_exit = false;
};

//==============================================================================
// Runtime (RAII initialization)
//==============================================================================
class Runtime {
    std::unique_ptr<cds::gc::HP> hp_gc_;
    std::optional<tbb::global_control> tbb_control_;

public:
    explicit Runtime(const RuntimeConfig& cfg = {}) {
        // 1. Configure mimalloc
        mi_option_set(mi_option_eager_commit, cfg.eager_commit ? 1 : 0);
        mi_option_set(mi_option_show_stats, cfg.show_stats_on_exit ? 1 : 0);
        if (cfg.large_os_pages) {
            mi_option_set(mi_option_large_os_pages, 1);
        }

        // 2. Initialize libcds
        cds::Initialize();
        hp_gc_ = std::make_unique<cds::gc::HP>(
            cfg.hp_hazard_ptr_count,
            cfg.hp_max_thread_count,
            cfg.hp_retired_threshold
        );

        // 3. Configure TBB
        int threads = cfg.num_threads > 0 
            ? cfg.num_threads 
            : static_cast<int>(std::thread::hardware_concurrency());
        tbb_control_.emplace(tbb::global_control::max_allowed_parallelism, threads);
    }

    ~Runtime() {
        tbb_control_.reset();
        hp_gc_.reset();
        cds::Terminate();
    }

    // Non-copyable, non-movable
    Runtime(const Runtime&) = delete;
    Runtime& operator=(const Runtime&) = delete;
    Runtime(Runtime&&) = delete;
    Runtime& operator=(Runtime&&) = delete;
};

//==============================================================================
// Thread Guard (RAII for libcds thread attachment)
//==============================================================================
class ThreadGuard {
public:
    ThreadGuard() {
        if (!cds::threading::Manager::isThreadAttached()) {
            cds::threading::Manager::attachThread();
        }
    }

    ~ThreadGuard() {
        cds::threading::Manager::detachThread();
    }

    ThreadGuard(const ThreadGuard&) = delete;
    ThreadGuard& operator=(const ThreadGuard&) = delete;
};

//==============================================================================
// MapReduce Engine
//==============================================================================
template<typename K, typename V>
class MapReduceEngine {
    Scheduler scheduler_;

public:
    explicit MapReduceEngine(int num_threads = 0)
        : scheduler_(num_threads) {}

    // Fast path: libcuckoo backend
    template<typename Input, typename MapFn, typename ReduceFn>
    FastHashMap<K, V> map_reduce(
        const std::vector<Input>& input,
        MapFn map_fn,
        ReduceFn reduce_fn)
    {
        const size_t num_threads = scheduler_.concurrency();

        // Thread-local accumulation
        struct alignas(64) LocalMap {
            MiUnorderedMap<K, V> map;
        };
        std::vector<LocalMap> local_maps(num_threads);

        // Map phase
        tbb::parallel_for(
            tbb::blocked_range<size_t>(0, input.size()),
            [&](const auto& r) {
                size_t tid = tbb::this_task_arena::current_thread_index();
                auto& local = local_maps[tid].map;

                for (size_t i = r.begin(); i < r.end(); ++i) {
                    for (auto& [key, value] : map_fn(input[i])) {
                        auto it = local.find(key);
                        if (it != local.end()) {
                            it->second = reduce_fn(it->second, value);
                        } else {
                            local.emplace(key, value);
                        }
                    }
                }
            }
        );

        // Reduce phase: merge to concurrent map
        FastHashMap<K, V> result(input.size() / 10 + 1);

        tbb::parallel_for(size_t(0), num_threads, [&](size_t tid) {
            for (auto& [key, value] : local_maps[tid].map) {
                result.upsert(key,
                    [&](V& existing) { existing = reduce_fn(existing, value); },
                    value);
            }
        });

        return result;
    }

    // Lock-free path: libcds backend
    template<typename Input, typename MapFn, typename ReduceFn>
    LockFreeHashMap<K, V> map_reduce_lockfree(
        const std::vector<Input>& input,
        MapFn map_fn,
        ReduceFn reduce_fn)
    {
        LockFreeHashMap<K, V> result(input.size() / 10 + 1);

        tbb::parallel_for(
            tbb::blocked_range<size_t>(0, input.size()),
            [&](const auto& r) {
                ThreadGuard guard;

                for (size_t i = r.begin(); i < r.end(); ++i) {
                    for (auto& [key, value] : map_fn(input[i])) {
                        // Try update first
                        bool updated = result.update(key, [&](V& v) {
                            v = reduce_fn(v, value);
                        });
                        
                        // If key didn't exist, insert
                        if (!updated) {
                            result.insert(key, value);
                        }
                    }
                }
            }
        );

        return result;
    }
};

//==============================================================================
// Pipeline
//==============================================================================
template<typename Input, typename Output>
class Pipeline {
    LockFreeQueue<Input> input_queue_;
    LockFreeQueue<Output> output_queue_;
    FastHashMap<std::string, size_t> metrics_;
    
    std::vector<std::thread> workers_;
    std::atomic<bool> running_{false};

public:
    explicit Pipeline(size_t queue_capacity = 10000)
        : input_queue_(queue_capacity)
        , output_queue_(queue_capacity) {}

    ~Pipeline() {
        stop();
    }

    template<typename TransformFn>
    void start(int num_workers, TransformFn transform) {
        running_ = true;
        
        for (int i = 0; i < num_workers; ++i) {
            workers_.emplace_back([this, transform] {
                ThreadGuard guard;
                
                Input in;
                std::vector<Output> batch;
                batch.reserve(100);

                while (running_ || input_queue_.size_approx() > 0) {
                    if (input_queue_.try_pop(in)) {
                        batch.push_back(transform(in));

                        if (batch.size() >= 100) {
                            output_queue_.push_bulk(batch.begin(), batch.size());
                            metrics_.upsert("processed",
                                [n = batch.size()](size_t& v) { v += n; },
                                batch.size());
                            batch.clear();
                        }
                    } else {
                        std::this_thread::yield();
                    }
                }

                // Flush remaining
                if (!batch.empty()) {
                    output_queue_.push_bulk(batch.begin(), batch.size());
                    metrics_.upsert("processed",
                        [n = batch.size()](size_t& v) { v += n; },
                        batch.size());
                }
            });
        }
    }

    void submit(Input item) {
        input_queue_.push(std::move(item));
    }

    template<typename It>
    void submit_bulk(It begin, size_t count) {
        input_queue_.push_bulk(begin, count);
    }

    bool try_get(Output& out) {
        return output_queue_.try_pop(out);
    }

    void stop() {
        running_ = false;
        for (auto& w : workers_) {
            if (w.joinable()) w.join();
        }
        workers_.clear();
    }

    size_t processed() const {
        size_t count = 0;
        metrics_.find("processed", count);
        return count;
    }

    size_t pending_input() const { return input_queue_.size_approx(); }
    size_t pending_output() const { return output_queue_.size_approx(); }
};

} // namespace rt
```

---


---

**Continued in:** [Part 3 - Usage & Rust Considerations](high_performance_concurrent_runtime_part3.md)
