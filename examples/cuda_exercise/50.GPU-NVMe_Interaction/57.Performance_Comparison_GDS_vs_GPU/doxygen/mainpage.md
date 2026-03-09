# Module 57: 57.Performance_Comparison_GDS_vs_GPU

## Overview

This module implements Brief description for 57.Performance_Comparison_GDS_vs_GPU

## Module Architecture

The module is organized into the following components:

- **common/**: Shared utilities, data structures, and helper functions
  - Reusable across different parts of the module
  - Common data structures and type definitions

- **host/**: CPU-side implementations
  - Pure C/C++ code without CUDA
  - Host functions and utilities
  - Platform-specific implementations

- **kernels/**: CUDA kernel implementations
  - Core GPU kernels
  - Reusable across different module features
  - Optimized compute-intensive operations

- **part_specific/**: Module-specific code
  - Feature-specific implementations
  - Integration code
  - Demonstrations and examples

## Key Components

### Core APIs

- `HostSubmission` / `HostBenchmark` (src/host): host-driven NVMe submission and latency/throughput harness
- Benchmark entry points `benchmark_mode1_gds` … `benchmark_mode6_hardware_dbc_gpu` (test/benchmarks)
- Common utilities in `common/benchmark_base.h` for timing and stats

### Data Structures

- `ReadResult`, `BenchmarkConfig`, `LatencyStats` (common/benchmark_base.h) capture timings and configuration
- `GpuNvmeQueueExt` (benchmark_mode6_hardware_dbc_gpu.cu) extends queue metadata for hardware DBC

### CUDA Kernels

- `sum_kernel.cu`: simple reduction over 4KB buffers used for post-I/O validation
- Mode 5/6 GPU command builders in benchmark sources: build NVMe commands and write doorbells from GPU

## Usage Examples

See the `test/` directory for comprehensive usage examples:

- `test/unit/`: Unit tests for individual components
- `test/integration/`: Integration tests for end-to-end workflows

## Building Documentation

From the build directory:
```bash
ninja doxygen_57_Performance_Comparison_GDS_vs_GPU
```

The generated HTML documentation will be available at:
```
build/50.GPU-NVMe_Interaction/57.Performance_Comparison_GDS_vs_GPU/doxygen/html/index.html
```

## Dependencies

- Module 53: NVMe VFIO host layer, device detection, doorbell helpers
- Module 54/55: Host/GPU buffer allocators and P2P queue mapping helpers
- `00.perf_common`: Shared performance timers and stats
- CUDA 13+, VFIO-bound NVMe, optional `/dev/gpu_p2p_nvme` for P2P mapping

## Performance Considerations

- Modes compare host vs GPU command build, MMIO vs daemon vs hardware DBC; ensure P2P module loaded for modes 2/4/5/6
- Mode 6 attempts hardware DBC (admin 0x7C) and falls back to pinned host when unavailable
- Warm caches and preallocate buffers to avoid skewing latency numbers

## See Also

- Module README.md for detailed learning materials
- Test files for usage examples
- Related modules: 53.NVMe_VFIO_Host_Layer, 55.CUDA_GPU_Memory, 56.GPU_Queue_GPU_Buffer
