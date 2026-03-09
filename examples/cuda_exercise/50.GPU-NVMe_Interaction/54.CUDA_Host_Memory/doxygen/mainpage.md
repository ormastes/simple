# Module 54: 54.CUDA_Host_Memory

## Overview

This module implements Brief description for 54.CUDA_Host_Memory

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

- CUDA pinned host buffer allocation (`cuda_host_buffer_*`, `cuda_host_pool_create`)
- Host I/O helpers for pinned buffers (`cuda_io_host_mem.*`)
- VFIO mapping helpers for host buffers (`cuda_host_map_iova`)

### Data Structures

- `Buffer`, `DmaBuf`, `HostPool` for pinned host allocations and DMA metadata
- Item size descriptors for I/O alignment

### CUDA Kernels

- Module focuses on host-side CUDA allocations; kernels are provided in higher modules (55/56)

## Usage Examples

See the `test/` directory for comprehensive usage examples:

- `test/unit/`: Unit tests for individual components
- `test/integration/`: Integration tests for end-to-end workflows

## Building Documentation

From the build directory:
```bash
ninja doxygen_54_CUDA_Host_Memory
```

The generated HTML documentation will be available at:
```
build/50.GPU-NVMe_Interaction/54.CUDA_Host_Memory/doxygen/html/index.html
```

## Dependencies

- Module 53 host mapper/VFIO (`mapper_host`, `host_io_host_mem`)
- CUDA 13+ for host-pinned allocations

## Performance Considerations

- Use page-aligned pinned buffers to minimize DMA setup overhead
- Prefer pool allocations (`cuda_host_pool_create`) to avoid repeated registration

## See Also

- Module README.md for detailed learning materials
- Test files for usage examples
- Related modules: 53.NVMe_VFIO_Host_Layer, 55.CUDA_GPU_Memory
