# High-Performance Concurrent Runtime Stack
## Complete Reference (TBB + moodycamel + libcuckoo + libcds + mimalloc)

**Part 1: Overview & Setup**
**Part of:** [High-Performance Concurrent Runtime Stack](high_performance_concurrent_runtime.md)


---

## Stack Overview

| Component | Library | Type | Purpose |
|-----------|---------|------|---------|
| **Scheduler** | TBB | Work-stealing | Parallel loops, tasks, reduction |
| **Queue** | moodycamel | Lock-free | Producer-consumer, message passing |
| **HashMap (fast)** | libcuckoo | Fine-grained locks | Maximum throughput |
| **HashMap (lock-free)** | libcds | Lock-free (HP/Epoch) | Bounded latency, real-time |
| **Allocator** | mimalloc | Thread-local heaps | Fast allocation, low fragmentation |

---

## Architecture

```
┌──────────────────────────────────────────────────────────────────┐
│                         Application                               │
├──────────────────────────────────────────────────────────────────┤
│                                                                   │
│   ┌─────────────────────────────────────────────────────────┐    │
│   │                    TBB Scheduler                         │    │
│   │  parallel_for │ parallel_reduce │ task_group │ flow_graph│    │
│   └─────────────────────────────────────────────────────────┘    │
│                              │                                    │
│          ┌───────────────────┼───────────────────┐               │
│          ▼                   ▼                   ▼               │
│   ┌─────────────┐    ┌─────────────┐    ┌─────────────┐         │
│   │ moodycamel  │    │ libcuckoo   │    │ libcds      │         │
│   │ Queue       │    │ HashMap     │    │ HashMap     │         │
│   │             │    │             │    │             │         │
│   │ Lock-free ✓ │    │ Fine-lock   │    │ Lock-free ✓ │         │
│   │ Bulk ops ✓  │    │ Fastest     │    │ HP/Epoch    │         │
│   └─────────────┘    └─────────────┘    └─────────────┘         │
│                                                                   │
├──────────────────────────────────────────────────────────────────┤
│                       mimalloc Allocator                          │
│   ┌────────────────┐ ┌────────────────┐ ┌────────────────┐       │
│   │ Thread-local   │ │ Size-class     │ │ Eager commit   │       │
│   │ heaps          │ │ segregation    │ │ (low latency)  │       │
│   └────────────────┘ └────────────────┘ └────────────────┘       │
└──────────────────────────────────────────────────────────────────┘
```

---

## Compatibility Matrix

| Library A | Library B | Works | Notes |
|-----------|-----------|-------|-------|
| TBB | moodycamel | ✅ | Independent systems |
| TBB | libcuckoo | ✅ | Both use std::atomic |
| TBB | libcds | ✅ | Attach threads to libcds GC |
| TBB | mimalloc | ✅ | Disable TBB malloc |
| moodycamel | libcuckoo | ✅ | No shared state |
| moodycamel | libcds | ✅ | No shared state |
| moodycamel | mimalloc | ✅ | Custom allocator trait |
| libcuckoo | libcds | ✅ | Use for different needs |
| libcuckoo | mimalloc | ✅ | Custom allocator |
| libcds | mimalloc | ✅ | libcds uses mimalloc for alloc, HP for safe deletion |

**All libraries work together with no conflicts.**

---

## Platform Support

| Library | x86/64 | ARM64 | RISC-V | Notes |
|---------|--------|-------|--------|-------|
| TBB | ✅ Excellent | ✅ Good | ⚠️ Experimental | Best on x86 |
| moodycamel | ✅ Excellent | ✅ Excellent | ✅ Good | Most portable |
| libcuckoo | ✅ Excellent | ✅ Good | ✅ Good | std::atomic only |
| libcds | ✅ Excellent | ✅ Good | ⚠️ Limited | Test on RISC-V |
| mimalloc | ✅ Excellent | ✅ Excellent | ✅ Good | Very portable |

---

## Project Setup

### Directory Structure

```
project/
├── CMakeLists.txt
├── include/
│   └── runtime/
│       ├── runtime.hpp
│       ├── queue.hpp
│       ├── hashmap.hpp
│       ├── scheduler.hpp
│       └── allocator.hpp
├── src/
│   └── main.cpp
└── rust_wrapper/          # Rust FFI bindings
    ├── Cargo.toml
    ├── build.rs
    └── src/
        └── lib.rs
```

### CMakeLists.txt

```cmake
cmake_minimum_required(VERSION 3.16)
project(concurrent_runtime CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3 -march=native -fPIC")

# ============ Dependencies ============

# TBB
find_package(TBB REQUIRED)

# mimalloc
find_package(mimalloc REQUIRED)

# libcds
find_package(PkgConfig QUIET)
if(PkgConfig_FOUND)
    pkg_check_modules(LIBCDS libcds)
endif()

if(NOT LIBCDS_FOUND)
    include(FetchContent)
    FetchContent_Declare(libcds
        GIT_REPOSITORY https://github.com/khizmax/libcds.git
        GIT_TAG v2.3.3)
    set(WITH_TESTS OFF CACHE BOOL "" FORCE)
    FetchContent_MakeAvailable(libcds)
    set(LIBCDS_LIBRARIES cds)
endif()

# Header-only: moodycamel, libcuckoo
include(FetchContent)

FetchContent_Declare(concurrentqueue
    GIT_REPOSITORY https://github.com/cameron314/concurrentqueue.git
    GIT_TAG v1.0.4)

FetchContent_Declare(libcuckoo
    GIT_REPOSITORY https://github.com/efficient/libcuckoo.git
    GIT_TAG master)

FetchContent_MakeAvailable(concurrentqueue libcuckoo)

# ============ Library ============

add_library(concurrent_runtime STATIC
    src/runtime.cpp
)

target_include_directories(concurrent_runtime PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}/include
    ${concurrentqueue_SOURCE_DIR}
    ${libcuckoo_SOURCE_DIR}
)

target_link_libraries(concurrent_runtime PUBLIC
    TBB::tbb
    mimalloc
    ${LIBCDS_LIBRARIES}
)

# Do NOT link TBB malloc - use mimalloc instead
# target_link_libraries(concurrent_runtime TBB::tbbmalloc)  # WRONG

# ============ Executable ============

add_executable(demo src/main.cpp)
target_link_libraries(demo concurrent_runtime)

# ============ Shared library for Rust FFI ============

add_library(concurrent_runtime_ffi SHARED
    src/ffi.cpp
)

target_include_directories(concurrent_runtime_ffi PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}/include
    ${concurrentqueue_SOURCE_DIR}
    ${libcuckoo_SOURCE_DIR}
)

target_link_libraries(concurrent_runtime_ffi PUBLIC
    TBB::tbb
    mimalloc
    ${LIBCDS_LIBRARIES}
)

set_target_properties(concurrent_runtime_ffi PROPERTIES
    OUTPUT_NAME "concurrent_runtime"
    POSITION_INDEPENDENT_CODE ON
)
```

---


---


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


---

## Usage Example

### src/main.cpp

```cpp
#include <runtime/runtime.hpp>
#include <iostream>
#include <sstream>
#include <chrono>

using namespace rt;
using namespace std::chrono;

// Helper: tokenize string into word counts
std::vector<std::pair<std::string, size_t>> tokenize(const std::string& doc) {
    std::vector<std::pair<std::string, size_t>> result;
    std::istringstream iss(doc);
    std::string word;
    while (iss >> word) {
        result.emplace_back(word, 1);
    }
    return result;
}

int main() {
    // Initialize runtime
    Runtime runtime({
        .num_threads = 0,  // auto-detect
        .eager_commit = true,
        .show_stats_on_exit = true
    });

    std::cout << "=== Concurrent Runtime Demo ===\n\n";

    //=== 1. Parallel Reduction ===
    {
        ThreadGuard guard;
        
        constexpr size_t N = 10'000'000;
        MiVector<double> data(N);
        for (size_t i = 0; i < N; ++i) {
            data[i] = static_cast<double>(i);
        }

        Scheduler sched;
        SumReducer<double> reducer(0.0);

        auto start = high_resolution_clock::now();

        sched.parallel_for_range(
            tbb::blocked_range<size_t>(0, N),
            [&](const auto& r) {
                double local = 0;
                for (size_t i = r.begin(); i < r.end(); ++i) {
                    local += data[i];
                }
                reducer.local() += local;
            }
        );

        double total = reducer.combine();
        auto elapsed = duration_cast<milliseconds>(high_resolution_clock::now() - start);

        std::cout << "1. Parallel Sum\n"
                  << "   Result: " << total << "\n"
                  << "   Time: " << elapsed.count() << " ms\n\n";
    }

    //=== 2. Lock-Free Queue ===
    {
        LockFreeQueue<int> queue;
        constexpr size_t N = 1'000'000;

        auto start = high_resolution_clock::now();

        // Bulk push
        MiVector<int> items(N);
        for (size_t i = 0; i < N; ++i) items[i] = static_cast<int>(i);
        queue.push_bulk(items.begin(), items.size());

        // Bulk pop
        MiVector<int> out(N);
        size_t popped = queue.try_pop_bulk(out.begin(), N);

        auto elapsed = duration_cast<microseconds>(high_resolution_clock::now() - start);

        std::cout << "2. Lock-Free Queue\n"
                  << "   Pushed/Popped: " << popped << "\n"
                  << "   Time: " << elapsed.count() << " μs\n\n";
    }

    //=== 3. Fast HashMap (libcuckoo) ===
    {
        FastHashMap<std::string, int> map(10000);
        Scheduler sched;

        auto start = high_resolution_clock::now();

        sched.parallel_for(10000, [&](size_t i) {
            map.insert("key_" + std::to_string(i), static_cast<int>(i));
        });

        auto elapsed = duration_cast<microseconds>(high_resolution_clock::now() - start);

        std::cout << "3. Fast HashMap (libcuckoo)\n"
                  << "   Size: " << map.size() << "\n"
                  << "   Time: " << elapsed.count() << " μs\n\n";
    }

    //=== 4. Lock-Free HashMap (libcds) ===
    {
        LockFreeHashMap<std::string, int> map(10000);

        auto start = high_resolution_clock::now();

        tbb::parallel_for(0, 10000, [&](int i) {
            ThreadGuard guard;
            map.insert("key_" + std::to_string(i), i);
        });

        auto elapsed = duration_cast<microseconds>(high_resolution_clock::now() - start);

        std::cout << "4. Lock-Free HashMap (libcds)\n"
                  << "   Size: " << map.size() << "\n"
                  << "   Time: " << elapsed.count() << " μs\n\n";
    }

    //=== 5. MapReduce ===
    {
        std::vector<std::string> docs(1000, 
            "the quick brown fox jumps over the lazy dog");

        MapReduceEngine<std::string, size_t> engine;

        auto start = high_resolution_clock::now();

        auto result = engine.map_reduce(
            docs,
            tokenize,
            std::plus<size_t>{}
        );

        auto elapsed = duration_cast<microseconds>(high_resolution_clock::now() - start);

        std::cout << "5. MapReduce (Word Count)\n"
                  << "   Unique words: " << result.size() << "\n"
                  << "   Time: " << elapsed.count() << " μs\n";

        auto table = result.lock_table();
        for (const auto& [word, count] : table) {
            std::cout << "   " << word << ": " << count << "\n";
        }
        std::cout << "\n";
    }

    //=== 6. Pipeline ===
    {
        Pipeline<int, int> pipeline;
        pipeline.start(4, [](int x) { return x * 2; });

        constexpr int N = 100000;
        for (int i = 0; i < N; ++i) {
            pipeline.submit(i);
        }

        std::this_thread::sleep_for(std::chrono::milliseconds(100));
        pipeline.stop();

        std::cout << "6. Pipeline\n"
                  << "   Processed: " << pipeline.processed() << "\n\n";
    }

    std::cout << "=== Memory Statistics ===\n";
    // mimalloc prints stats on exit due to show_stats_on_exit = true

    return 0;
}
```

---

## Rust Wrapper Considerations

### Two Approaches

| Approach | Pros | Cons |
|----------|------|------|
| **Use native Rust crates** | Idiomatic, safe, maintained | Different behavior/perf |
| **Create FFI wrappers** | Exact same behavior | Unsafe, maintenance burden |

### Native Rust Equivalents

| C++ Library | Rust Crate | Notes |
|-------------|------------|-------|
| TBB | `rayon` | Similar work-stealing |
| moodycamel | `crossbeam-queue` | Lock-free queues |
| libcuckoo | `dashmap` | Sharded locks |
| libcds | `flurry` | Epoch-based lock-free |
| mimalloc | `mimalloc` | Direct binding |

### Native Rust Stack (Recommended)

```toml
# Cargo.toml
[package]
name = "concurrent_runtime"
version = "0.1.0"
edition = "2021"

[dependencies]
rayon = "1.10"
crossbeam = "0.8"
dashmap = "6.0"
flurry = "0.5"
mimalloc = { version = "0.1", features = ["local_dynamic_tls"] }
parking_lot = "0.12"

[profile.release]
lto = "fat"
codegen-units = 1
opt-level = 3
```

```rust
// src/lib.rs
use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

pub mod queue {
    use crossbeam::queue::{ArrayQueue, SegQueue};

    /// Bounded lock-free queue
    pub struct BoundedQueue<T>(ArrayQueue<T>);

    impl<T> BoundedQueue<T> {
        pub fn new(capacity: usize) -> Self {
            Self(ArrayQueue::new(capacity))
        }

        pub fn push(&self, item: T) -> Result<(), T> {
            self.0.push(item)
        }

        pub fn pop(&self) -> Option<T> {
            self.0.pop()
        }

        pub fn len(&self) -> usize {
            self.0.len()
        }

        pub fn is_empty(&self) -> bool {
            self.0.is_empty()
        }
    }

    /// Unbounded lock-free queue
    pub struct UnboundedQueue<T>(SegQueue<T>);

    impl<T> UnboundedQueue<T> {
        pub fn new() -> Self {
            Self(SegQueue::new())
        }

        pub fn push(&self, item: T) {
            self.0.push(item);
        }

        pub fn pop(&self) -> Option<T> {
            self.0.pop()
        }

        pub fn len(&self) -> usize {
            self.0.len()
        }
    }
}

pub mod hashmap {
    use dashmap::DashMap;
    use flurry::HashMap as FlurryMap;
    use std::hash::Hash;
    use std::sync::Arc;

    /// Fast HashMap (like libcuckoo)
    pub struct FastHashMap<K, V>(DashMap<K, V>);

    impl<K: Eq + Hash, V> FastHashMap<K, V> {
        pub fn new() -> Self {
            Self(DashMap::new())
        }

        pub fn with_capacity(capacity: usize) -> Self {
            Self(DashMap::with_capacity(capacity))
        }

        pub fn insert(&self, key: K, value: V) {
            self.0.insert(key, value);
        }

        pub fn get(&self, key: &K) -> Option<dashmap::mapref::one::Ref<'_, K, V>> {
            self.0.get(key)
        }

        pub fn remove(&self, key: &K) -> Option<(K, V)> {
            self.0.remove(key)
        }

        pub fn len(&self) -> usize {
            self.0.len()
        }
    }

    impl<K: Eq + Hash + Clone, V: Clone> FastHashMap<K, V> {
        pub fn get_clone(&self, key: &K) -> Option<V> {
            self.0.get(key).map(|r| r.value().clone())
        }
    }

    /// Lock-free HashMap (like libcds)
    pub struct LockFreeHashMap<K, V>(Arc<FlurryMap<K, V>>);

    impl<K: Eq + Hash + Clone, V: Clone> LockFreeHashMap<K, V> {
        pub fn new() -> Self {
            Self(Arc::new(FlurryMap::new()))
        }

        pub fn insert(&self, key: K, value: V) {
            let guard = self.0.guard();
            self.0.insert(key, value, &guard);
        }

        pub fn get(&self, key: &K) -> Option<V> {
            let guard = self.0.guard();
            self.0.get(key, &guard).cloned()
        }

        pub fn remove(&self, key: &K) -> Option<V> {
            let guard = self.0.guard();
            self.0.remove(key, &guard).cloned()
        }

        pub fn len(&self) -> usize {
            let guard = self.0.guard();
            self.0.len()
        }
    }
}

pub mod scheduler {
    use rayon::prelude::*;

    /// Parallel iterator operations
    pub fn parallel_for<T, F>(items: &[T], f: F)
    where
        T: Sync,
        F: Fn(&T) + Sync + Send,
    {
        items.par_iter().for_each(f);
    }

    pub fn parallel_map<T, R, F>(items: &[T], f: F) -> Vec<R>
    where
        T: Sync,
        R: Send,
        F: Fn(&T) -> R + Sync + Send,
    {
        items.par_iter().map(f).collect()
    }

    pub fn parallel_reduce<T, R, F, G>(items: &[T], identity: R, f: F, reduce: G) -> R
    where
        T: Sync,
        R: Send + Clone,
        F: Fn(&T) -> R + Sync + Send,
        G: Fn(R, R) -> R + Sync + Send,
    {
        items.par_iter().map(f).reduce(|| identity.clone(), reduce)
    }
}

pub mod mapreduce {
    use crate::hashmap::FastHashMap;
    use rayon::prelude::*;
    use std::collections::HashMap;
    use std::hash::Hash;

    pub fn map_reduce<T, K, V, M, R>(
        input: &[T],
        mapper: M,
        reducer: R,
    ) -> FastHashMap<K, V>
    where
        T: Sync,
        K: Eq + Hash + Clone + Send + Sync,
        V: Clone + Send + Sync,
        M: Fn(&T) -> Vec<(K, V)> + Sync + Send,
        R: Fn(V, V) -> V + Sync + Send + Copy,
    {
        // Thread-local maps
        let local_maps: Vec<HashMap<K, V>> = input
            .par_chunks(1000)
            .map(|chunk| {
                let mut local = HashMap::new();
                for item in chunk {
                    for (k, v) in mapper(item) {
                        local
                            .entry(k)
                            .and_modify(|e| *e = reducer(e.clone(), v.clone()))
                            .or_insert(v);
                    }
                }
                local
            })
            .collect();

        // Merge
        let result = FastHashMap::new();
        for local in local_maps {
            for (k, v) in local {
                if let Some(existing) = result.get_clone(&k) {
                    result.insert(k, reducer(existing, v));
                } else {
                    result.insert(k, v);
                }
            }
        }
        result
    }
}
```

### FFI Wrapper (If Needed)

For cases where you need **exact same behavior** as C++ libraries:

#### src/ffi.cpp

```cpp
// C FFI interface for Rust
#include <runtime/runtime.hpp>
#include <cstdint>
#include <cstring>

extern "C" {

//==============================================================================
// Runtime
//==============================================================================
struct RuntimeHandle {
    rt::Runtime* runtime;
};

RuntimeHandle* runtime_create(int num_threads) {
    auto* handle = new RuntimeHandle;
    handle->runtime = new rt::Runtime({.num_threads = num_threads});
    return handle;
}

void runtime_destroy(RuntimeHandle* handle) {
    delete handle->runtime;
    delete handle;
}

//==============================================================================
// Lock-Free Queue
//==============================================================================
struct QueueHandle {
    rt::LockFreeQueue<int64_t>* queue;
};

QueueHandle* queue_create(size_t capacity) {
    auto* handle = new QueueHandle;
    handle->queue = new rt::LockFreeQueue<int64_t>(capacity);
    return handle;
}

void queue_destroy(QueueHandle* handle) {
    delete handle->queue;
    delete handle;
}

void queue_push(QueueHandle* handle, int64_t value) {
    handle->queue->push(value);
}

int32_t queue_try_pop(QueueHandle* handle, int64_t* out) {
    return handle->queue->try_pop(*out) ? 1 : 0;
}

size_t queue_size(QueueHandle* handle) {
    return handle->queue->size_approx();
}

//==============================================================================
// Fast HashMap
//==============================================================================
struct FastMapHandle {
    rt::FastHashMap<std::string, int64_t>* map;
};

FastMapHandle* fastmap_create(size_t capacity) {
    auto* handle = new FastMapHandle;
    handle->map = new rt::FastHashMap<std::string, int64_t>(capacity);
    return handle;
}

void fastmap_destroy(FastMapHandle* handle) {
    delete handle->map;
    delete handle;
}

void fastmap_insert(FastMapHandle* handle, const char* key, int64_t value) {
    handle->map->insert(key, value);
}

int32_t fastmap_get(FastMapHandle* handle, const char* key, int64_t* out) {
    return handle->map->find(key, *out) ? 1 : 0;
}

int32_t fastmap_remove(FastMapHandle* handle, const char* key) {
    return handle->map->erase(key) ? 1 : 0;
}

size_t fastmap_size(FastMapHandle* handle) {
    return handle->map->size();
}

//==============================================================================
// Lock-Free HashMap
//==============================================================================
struct LockFreeMapHandle {
    rt::LockFreeHashMap<std::string, int64_t>* map;
};

LockFreeMapHandle* lfmap_create(size_t capacity) {
    auto* handle = new LockFreeMapHandle;
    handle->map = new rt::LockFreeHashMap<std::string, int64_t>(capacity);
    return handle;
}

void lfmap_destroy(LockFreeMapHandle* handle) {
    delete handle->map;
    delete handle;
}

void lfmap_insert(LockFreeMapHandle* handle, const char* key, int64_t value) {
    handle->map->insert(key, value);
}

int32_t lfmap_get(LockFreeMapHandle* handle, const char* key, int64_t* out) {
    return handle->map->find(key, *out) ? 1 : 0;
}

int32_t lfmap_remove(LockFreeMapHandle* handle, const char* key) {
    return handle->map->erase(key) ? 1 : 0;
}

size_t lfmap_size(LockFreeMapHandle* handle) {
    return handle->map->size();
}

//==============================================================================
// Thread Guard (must call when using libcds from Rust threads)
//==============================================================================
void thread_attach() {
    cds::threading::Manager::attachThread();
}

void thread_detach() {
    cds::threading::Manager::detachThread();
}

} // extern "C"
```

#### rust_wrapper/Cargo.toml

```toml
[package]
name = "concurrent_runtime_sys"
version = "0.1.0"
edition = "2021"
build = "build.rs"

[lib]
crate-type = ["lib"]

[dependencies]
libc = "0.2"

[build-dependencies]
cc = "1.0"
pkg-config = "0.3"
```

#### rust_wrapper/build.rs

```rust
use std::env;
use std::path::PathBuf;

fn main() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let project_root = PathBuf::from(&manifest_dir).parent().unwrap().to_path_buf();
    let build_dir = project_root.join("build");

    // Link to the C++ shared library
    println!("cargo:rustc-link-search=native={}", build_dir.display());
    println!("cargo:rustc-link-lib=dylib=concurrent_runtime");

    // Link TBB
    println!("cargo:rustc-link-lib=dylib=tbb");

    // Link mimalloc
    println!("cargo:rustc-link-lib=dylib=mimalloc");

    // Link libcds
    println!("cargo:rustc-link-lib=dylib=cds");

    // Link C++ stdlib
    println!("cargo:rustc-link-lib=dylib=stdc++");

    // Rebuild if C++ changes
    println!("cargo:rerun-if-changed=../src/ffi.cpp");
}
```

#### rust_wrapper/src/lib.rs

```rust
//! Rust bindings to C++ concurrent runtime

use libc::{c_char, c_int, size_t};
use std::ffi::CString;

// Opaque handles
#[repr(C)]
pub struct RuntimeHandle {
    _private: [u8; 0],
}

#[repr(C)]
pub struct QueueHandle {
    _private: [u8; 0],
}

#[repr(C)]
pub struct FastMapHandle {
    _private: [u8; 0],
}

#[repr(C)]
pub struct LockFreeMapHandle {
    _private: [u8; 0],
}

// FFI declarations
extern "C" {
    // Runtime
    fn runtime_create(num_threads: c_int) -> *mut RuntimeHandle;
    fn runtime_destroy(handle: *mut RuntimeHandle);

    // Queue
    fn queue_create(capacity: size_t) -> *mut QueueHandle;
    fn queue_destroy(handle: *mut QueueHandle);
    fn queue_push(handle: *mut QueueHandle, value: i64);
    fn queue_try_pop(handle: *mut QueueHandle, out: *mut i64) -> i32;
    fn queue_size(handle: *mut QueueHandle) -> size_t;

    // Fast HashMap
    fn fastmap_create(capacity: size_t) -> *mut FastMapHandle;
    fn fastmap_destroy(handle: *mut FastMapHandle);
    fn fastmap_insert(handle: *mut FastMapHandle, key: *const c_char, value: i64);
    fn fastmap_get(handle: *mut FastMapHandle, key: *const c_char, out: *mut i64) -> i32;
    fn fastmap_remove(handle: *mut FastMapHandle, key: *const c_char) -> i32;
    fn fastmap_size(handle: *mut FastMapHandle) -> size_t;

    // Lock-Free HashMap
    fn lfmap_create(capacity: size_t) -> *mut LockFreeMapHandle;
    fn lfmap_destroy(handle: *mut LockFreeMapHandle);
    fn lfmap_insert(handle: *mut LockFreeMapHandle, key: *const c_char, value: i64);
    fn lfmap_get(handle: *mut LockFreeMapHandle, key: *const c_char, out: *mut i64) -> i32;
    fn lfmap_remove(handle: *mut LockFreeMapHandle, key: *const c_char) -> i32;
    fn lfmap_size(handle: *mut LockFreeMapHandle) -> size_t;

    // Thread management
    fn thread_attach();
    fn thread_detach();
}

//==============================================================================
// Safe Rust Wrappers
//==============================================================================

/// Runtime handle (RAII)
pub struct Runtime {
    handle: *mut RuntimeHandle,
}

impl Runtime {
    pub fn new(num_threads: i32) -> Self {
        unsafe {
            Self {
                handle: runtime_create(num_threads),
            }
        }
    }
}

impl Drop for Runtime {
    fn drop(&mut self) {
        unsafe {
            runtime_destroy(self.handle);
        }
    }
}

unsafe impl Send for Runtime {}
unsafe impl Sync for Runtime {}

/// Lock-free queue
pub struct Queue {
    handle: *mut QueueHandle,
}

impl Queue {
    pub fn new(capacity: usize) -> Self {
        unsafe {
            Self {
                handle: queue_create(capacity),
            }
        }
    }

    pub fn push(&self, value: i64) {
        unsafe {
            queue_push(self.handle, value);
        }
    }

    pub fn try_pop(&self) -> Option<i64> {
        let mut value: i64 = 0;
        unsafe {
            if queue_try_pop(self.handle, &mut value) != 0 {
                Some(value)
            } else {
                None
            }
        }
    }

    pub fn len(&self) -> usize {
        unsafe { queue_size(self.handle) }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl Drop for Queue {
    fn drop(&mut self) {
        unsafe {
            queue_destroy(self.handle);
        }
    }
}

unsafe impl Send for Queue {}
unsafe impl Sync for Queue {}

/// Fast HashMap (libcuckoo)
pub struct FastMap {
    handle: *mut FastMapHandle,
}

impl FastMap {
    pub fn new(capacity: usize) -> Self {
        unsafe {
            Self {
                handle: fastmap_create(capacity),
            }
        }
    }

    pub fn insert(&self, key: &str, value: i64) {
        let c_key = CString::new(key).unwrap();
        unsafe {
            fastmap_insert(self.handle, c_key.as_ptr(), value);
        }
    }

    pub fn get(&self, key: &str) -> Option<i64> {
        let c_key = CString::new(key).unwrap();
        let mut value: i64 = 0;
        unsafe {
            if fastmap_get(self.handle, c_key.as_ptr(), &mut value) != 0 {
                Some(value)
            } else {
                None
            }
        }
    }

    pub fn remove(&self, key: &str) -> bool {
        let c_key = CString::new(key).unwrap();
        unsafe { fastmap_remove(self.handle, c_key.as_ptr()) != 0 }
    }

    pub fn len(&self) -> usize {
        unsafe { fastmap_size(self.handle) }
    }
}

impl Drop for FastMap {
    fn drop(&mut self) {
        unsafe {
            fastmap_destroy(self.handle);
        }
    }
}

unsafe impl Send for FastMap {}
unsafe impl Sync for FastMap {}

/// Lock-Free HashMap (libcds)
pub struct LockFreeMap {
    handle: *mut LockFreeMapHandle,
}

impl LockFreeMap {
    pub fn new(capacity: usize) -> Self {
        unsafe {
            Self {
                handle: lfmap_create(capacity),
            }
        }
    }

    pub fn insert(&self, key: &str, value: i64) {
        let c_key = CString::new(key).unwrap();
        unsafe {
            lfmap_insert(self.handle, c_key.as_ptr(), value);
        }
    }

    pub fn get(&self, key: &str) -> Option<i64> {
        let c_key = CString::new(key).unwrap();
        let mut value: i64 = 0;
        unsafe {
            if lfmap_get(self.handle, c_key.as_ptr(), &mut value) != 0 {
                Some(value)
            } else {
                None
            }
        }
    }

    pub fn remove(&self, key: &str) -> bool {
        let c_key = CString::new(key).unwrap();
        unsafe { lfmap_remove(self.handle, c_key.as_ptr()) != 0 }
    }

    pub fn len(&self) -> usize {
        unsafe { lfmap_size(self.handle) }
    }
}

impl Drop for LockFreeMap {
    fn drop(&mut self) {
        unsafe {
            lfmap_destroy(self.handle);
        }
    }
}

unsafe impl Send for LockFreeMap {}
unsafe impl Sync for LockFreeMap {}

/// Thread guard for libcds
pub struct ThreadGuard;

impl ThreadGuard {
    pub fn new() -> Self {
        unsafe {
            thread_attach();
        }
        Self
    }
}

impl Drop for ThreadGuard {
    fn drop(&mut self) {
        unsafe {
            thread_detach();
        }
    }
}

//==============================================================================
// Tests
//==============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;

    #[test]
    fn test_queue() {
        let _runtime = Runtime::new(4);
        let queue = Queue::new(1000);

        queue.push(42);
        queue.push(43);

        assert_eq!(queue.try_pop(), Some(42));
        assert_eq!(queue.try_pop(), Some(43));
        assert_eq!(queue.try_pop(), None);
    }

    #[test]
    fn test_fast_map() {
        let _runtime = Runtime::new(4);
        let map = FastMap::new(100);

        map.insert("hello", 42);
        assert_eq!(map.get("hello"), Some(42));
        assert_eq!(map.get("world"), None);

        map.remove("hello");
        assert_eq!(map.get("hello"), None);
    }

    #[test]
    fn test_lockfree_map() {
        let _runtime = Runtime::new(4);
        let map = LockFreeMap::new(100);

        let _guard = ThreadGuard::new();

        map.insert("hello", 42);
        assert_eq!(map.get("hello"), Some(42));
    }

    #[test]
    fn test_concurrent_access() {
        let runtime = Runtime::new(4);
        let queue = std::sync::Arc::new(Queue::new(10000));

        let mut handles = vec![];

        // Producers
        for i in 0..4 {
            let q = queue.clone();
            handles.push(thread::spawn(move || {
                for j in 0..1000 {
                    q.push((i * 1000 + j) as i64);
                }
            }));
        }

        // Consumer
        let q = queue.clone();
        handles.push(thread::spawn(move || {
            let mut count = 0;
            while count < 4000 {
                if q.try_pop().is_some() {
                    count += 1;
                }
            }
        }));

        for h in handles {
            h.join().unwrap();
        }
    }
}
```

---


---


---

## Recommendation Summary

| Use Case | Approach |
|----------|----------|
| **New Rust project** | Use native Rust crates (rayon, crossbeam, dashmap, flurry) |
| **Need exact C++ behavior** | Create FFI wrapper as shown above |
| **Mixed C++/Rust codebase** | FFI wrapper with shared runtime |
| **Maximum performance testing** | Benchmark both approaches |

### Native Rust vs FFI Trade-offs

| Aspect | Native Rust | FFI Wrapper |
|--------|-------------|-------------|
| **Safety** | ✅ Full | ⚠️ Unsafe boundaries |
| **Idiomatic** | ✅ Yes | ❌ C-style API |
| **Performance** | ✅ Same or better | ✅ Exact same as C++ |
| **Maintenance** | ✅ Community maintained | ❌ Self-maintained |
| **Debug** | ✅ Easy | ⚠️ Cross-language |
| **Behavior match** | ⚠️ Different libs | ✅ Exact same |

---

## Final Summary

### What Works Together

| Component | Status | Notes |
|-----------|--------|-------|
| TBB + moodycamel | ✅ | Independent |
| TBB + libcuckoo | ✅ | Both use std::atomic |
| TBB + libcds | ✅ | Use ThreadGuard |
| TBB + mimalloc | ✅ | Disable TBB malloc |
| moodycamel + libcuckoo | ✅ | No shared state |
| moodycamel + libcds | ✅ | No shared state |
| moodycamel + mimalloc | ✅ | Custom allocator |
| libcuckoo + libcds | ✅ | Different use cases |
| libcuckoo + mimalloc | ✅ | Custom allocator |
| **libcds + mimalloc** | **✅** | **libcds uses mimalloc for alloc, HP for safe deletion** |

### When to Use What

| Need | Use This |
|------|----------|
| Maximum HashMap throughput | libcuckoo (FastHashMap) |
| Lock-free HashMap guarantee | libcds (LockFreeHashMap) |
| Lock-free queue + bulk ops | moodycamel (LockFreeQueue) |
| Parallel loops/reduction | TBB (Scheduler, Reducer) |
| Fast memory allocation | mimalloc (global) |
| Rust interop | Native crates or FFI wrapper |

---

**Previous:** [Part 3 - Usage & Rust Considerations](high_performance_concurrent_runtime_part3.md)
