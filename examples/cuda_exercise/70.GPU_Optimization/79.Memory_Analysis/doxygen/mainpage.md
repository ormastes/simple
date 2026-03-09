# Module 79: Memory Profiling and Analysis

## Overview

This module provides GPU memory profiling, bandwidth measurement, and memory optimization tools. It includes a tracked allocator for leak detection, STREAM-like bandwidth benchmarks, a free-list memory pool, optional NVML integration for real-time GPU monitoring, and Python-based visualization.

## Module Architecture

The module is organized into the following components:

- **profiling/**: Memory measurement and tracking
  - `memory_profiler.cu` - MemoryTracker with per-allocation labels, peak tracking, and leak detection
  - `bandwidth_test.cu` - STREAM-like Copy/Scale/Add/Triad GPU bandwidth benchmarks

- **tools/**: GPU monitoring utilities
  - `nvml_wrapper.cu` - Conditional NVML integration for memory, utilization, and temperature queries

- **optimizations/**: Memory allocation strategies
  - `memory_pool.cu` - Free-list pool allocator to avoid repeated cudaMalloc/cudaFree

- **python/**: Analysis and visualization
  - `visualize_memory.py` - matplotlib timeline plot from JSON allocation logs

## Key Components

### MemoryTracker
Wraps cudaMalloc/cudaFree to record allocations with labels, track current and peak usage, and detect leaks.

### BandwidthResult / run_bandwidth_test()
STREAM-style benchmarks reporting Copy, Scale, Add, and Triad bandwidth in GB/s.

### MemoryPool
Pre-allocates a large GPU memory region and serves sub-allocations via first-fit free-list with automatic coalescing.

### NVML Wrapper
Queries GPU memory info, utilization rates, and temperature (when NVML is available).

## Building

```bash
ninja 79_Memory_Analysis_test
ninja doxygen_79_Memory_Analysis
```

## Dependencies

- CUDA Toolkit
- CudaCustomLib (shared utilities)
- NVML (optional, for nvml_wrapper)
- matplotlib (optional, for Python visualization)

## See Also

- Module README.md for detailed learning materials
- Test files for usage examples
