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

**Continued in:** [Part 2 - Runtime Implementation](high_performance_concurrent_runtime_part2.md)
