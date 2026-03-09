# Hardcoded Values Documentation

This document lists all hardcoded page sizes (4096) and LBA sizes (512) found in the source code,
categorized by their purpose and location.

## Refactoring Status (2024-12)

**COMPLETED:** Key files have been refactored to use `NvmeDevice` getters instead of hardcoded values:
- `benchmark_constants.h` - Added `get_lba_size_from_device()` and `get_page_size_from_device()`
- `perf_test_helper.h` - Added `get_chunk_size()` and `get_lba_size()` helpers
- `benchmark_mode5_dbc_daemon_gpu_command.cu` - Uses device values for io_size and page_size
- `cuda_io_host_mem.cpp` - Renamed `kPage` to `kDefaultPageSize` with documentation

## Overview

| Category | 4096 (Page Size) | 512 (LBA Size) |
|----------|------------------|----------------|
| Constants/Defaults | 15 | 25 |
| Test Values | 35+ | 20+ |
| Alignment | 10+ | 2 |
| Buffer Sizes | 20+ | 5 |

---

## 1. NvmeDevice Structure (Source of Truth)

Location: `src/host/mapper/mapper_host.cpp:90-103`

```cpp
struct NvmeDevice {
  size_t page_size{4096};     // Dynamic, initialized from CAP.MPSMIN
  uint8_t mps_value{0};       // Memory Page Size value for CC.MPS
  uint32_t lba_size{512};     // Default 512B, can be 4096B
  ItemSize item_size{};       // Configured during nvme_open()
  // ...
};
```

**Key APIs:**
- `nvme_get_page_size(NvmeDevice* d)` - Returns device page size (default 4096)
- `nvme_get_lba_size(NvmeDevice* d)` - Returns LBA size (default 512)
- `nvme_set_page_size(NvmeDevice* d, size_t page_size)` - Configure before controller enable

---

## 2. Hardcoded 4096 (Page Size) Locations

### 2.1 Source Code - Constants & Defaults

| File | Line | Context | Recommendation |
|------|------|---------|----------------|
| `src/host/mapper/mapper_host.cpp` | 31, 96 | `kPage = 4096`, `page_size{4096}` | Source of truth - OK |
| `src/host/mapper/mapper_host.cpp` | 218, 513, 514 | Page size validation/fallback | OK (fallback defaults) |
| `src/cuda_host/io/cuda_io_host_mem.cpp` | 21 | `constexpr size_t kPage = 4096` | **Should use device->page_size** |
| `src/cuda_gpu/mapper/mapper_gpu.cpp` | 315 | `cudaMalloc(&dummy_gpu_ptr, 4096)` | OK (dummy allocation) |

### 2.2 Test Files - Performance Tests

| File | Line | Usage |
|------|------|-------|
| `test/performance_test/mode0_baseline.cu` | 43, 185, 198 | `CHUNK_SIZE = 4096`, alignment |
| `test/performance_test/mode1_host_mmio_pinned.cu` | 49 | `CHUNK_SIZE = 4096` |
| `test/performance_test/mode2_host_daemon_gpu.cu` | 109-111 | 4096-byte alignment |
| `test/performance_test/mode3_host_dbc_host.cu` | - | Chunk size |
| `test/performance_test/mode4_host_dbc_gpu.cu` | 228 | Shadow doorbell page_size |
| `test/performance_test/mode5_gpu_initiated_dbc.cu` | 43 | `CHUNK_SIZE = 4096` |
| `test/performance_test/perf_test_helper.h` | 47 | `DEFAULT_CHUNK_SIZE = 4096` |
| `test/performance_test/check_oacs_helper.h` | 25, 28, 37, 99 | Identify controller buffer |

### 2.3 Benchmark Files (Module 57)

| File | Line | Usage |
|------|------|-------|
| `benchmark_constants.h` | 24, 30 | `BUFFER_SIZE_4KB`, `PAGE_SIZE` |
| `benchmark_mode1_gds.cpp` | 205, 268, 427 | Page alignment, buffer size |
| `benchmark_mode2_host_daemon_gpu_mem.cpp` | 82, 90-96, 127, 280 | Buffer alloc, IOVA mapping |
| `benchmark_mode3_host_daemon.cpp` | 147, 181, 197, 283 | GPU buffer, page alignment |
| `benchmark_mode4_dbc_shadow_gpu.cpp` | 117, 125, 283 | Buffer alloc, page size |
| `benchmark_mode5_dbc_daemon_gpu_command.cu` | 431, 440, 502, 517, 557, 570, 616, 718 | I/O size, PRP2 calc |
| `benchmark_mode6_hardware_dbc_gpu.cu` | 546, 781, 845 | Doorbell size, I/O size |
| `benchmark_gds.cu` | 86, 100, 217 | Buffer size default |
| `gds_benchmark.cpp` | 38, 269 | `BLOCK_SIZE = 4096` |
| `host_submission.cpp` | 67, 88, 93, 135, 153 | Item size, buffer alloc |
| `host_benchmark.cpp` | 79 | Bandwidth calculation |

### 2.4 Unit Tests

| File | Line | Usage |
|------|------|-------|
| `test/unit/host/test_host_io_host_mem.cpp` | 16 | `kPage = 4096` |
| `test/unit/host/test_prp_edge_cases.cpp` | 27, 438 | Page constant, PRP entries/page |
| `test/unit/host/test_template_combinations.cpp` | 8 | `kPage = 4096` |
| `test/unit/common/test_memory_buffer_utils.cpp` | 93, 96, 101, 149, 153 | Test buffer sizes |
| `test/unit/part_specific/test_nvme_page_size.cpp` | 21-23, 29, 52 | Page size validation |
| `test/unit/queue/test_factory_methods.cpp` | 66, 76, 214, 231 | LBA size tests |

### 2.5 DmaBuf/Memory_types.h Alignment

| File | Line | Context |
|------|------|---------|
| `src/common/memory/memory_types.h` | 91, 94, 96, 99 | `& ~4095UL` alignment masks |

**Note:** These are alignment operations using `4095` mask (4096-1). Should consider using `page_size - 1` for dynamic page sizes.

---

## 3. Hardcoded 512 (LBA Size) Locations

### 3.1 Source Code - Defaults

| File | Line | Context | Recommendation |
|------|------|---------|----------------|
| `src/host/mapper/mapper_host.cpp` | 98, 362-369, 393, 608, 614 | Default LBA, supported sizes | Source of truth - OK |
| `src/common/device/nvme_feature.h` | 189 | `lba_size_{512}` | OK (default) |
| `src/common/device/nvme_feature.cpp` | 91 | Kernel reports 512-byte sectors | OK (standard) |

### 3.2 Configuration Files

| File | Line | Context |
|------|------|---------|
| `test/helper/nvme_config.h` | 66, 75, 84, 96 | Default LBA config, validation |
| `test/helper/setup_helper.h` | 500, 519 | Default LBA for NvmeSetupTask |
| `test/helper/system_test_config.h` | 35, 43, 76 | Default LBA config |
| `test/helper/nvme_test_helper.h` | 112 | `cfg.lba_size = 512` |
| `00.perf_common/include/perf_config.h` | 54 | `nvme_lba_size_ = get_env_uint32("NVME_LBA_SIZE", 512)` |

### 3.3 Test/Benchmark Files

| File | Line | Usage |
|------|------|-------|
| `test/performance_test/mode0_baseline.cu` | 161-162 | `actual_lba_size = 512` |
| `test/performance_test/mode1_host_mmio_pinned.cu` | 174 | `lba_size = 512` |
| `test/performance_test/mode2_host_daemon_gpu.cu` | 69 | `lba_size_ = 512` |
| `test/performance_test/mode3_host_dbc_host.cu` | 109 | `lba_size_ = 512` |
| `test/performance_test/mode4_host_dbc_gpu.cu` | 257 | `chunk_size / 512 - 1` (NLB calc) |
| `test/performance_test/mode5_gpu_initiated_dbc.cu` | 305 | `lba_size = 512` |
| `benchmark_mode5_dbc_daemon_gpu_command.cu` | 656 | `NVME_LBA_SIZE` default |
| `benchmark_mode6_hardware_dbc_gpu.cu` | 222, 234, 378 | LBA calculations |
| `benchmark_mode1_gds.cpp` | 508, 512 | nvme_open call |
| `benchmark_mode4_dbc_shadow_gpu.cpp` | 364, 368 | nvme_open call |
| `benchmark_gds.cu` | 110, 255 | nvme_open, NLB calculation |
| `gds_benchmark.cpp` | 44 | nvme_open call |
| `host_submission.cpp` | 51 | `lba_size_(512)` |

### 3.4 File Utilities

| File | Line | Context |
|------|------|---------|
| `src/common/io/nvme_file_utils.h` | 33, 40, 50, 57, 84, 98, 123 | Default sector_size param |
| `src/common/io/nvme_file_utils.cpp` | 77, 170 | Fallback sector size |

---

## 4. PRP List Buffer Naming Convention

The PRP (Physical Region Page) list is used for NVMe commands that span more than 2 pages.

### 4.1 DmaBuf Structure Fields

Location: `src/common/memory/memory_types.h:78-80`

```cpp
struct DmaBuf {
    void*     prplist_host{nullptr};   // Host virtual address of PRP list
    uint64_t  prplist_iova{0};         // IOVA address for NVMe controller
    size_t    prplist_bytes{0};        // Size of PRP list in bytes
    // ...

    // Helper methods:
    uint64_t prplist_iova_aligned() const;  // Page-aligned IOVA
    size_t prplist_map_size() const;        // VFIO mapping size
    size_t prplist_capacity() const;        // Number of PRP entries (prplist_bytes / 8)
};
```

### 4.2 PRP List Size Calculation

Location: `src/host/memory/host_memory_buffer.cpp:67-85`

```cpp
// Maximum PRP entries per page: page_size / 8 (each PRP entry is 8 bytes)
// NVMe spec limits PRP lists to 2 pages maximum
// Maximum PRP entries: (page_size / 8) * 2
// Maximum data pages with PRPs: (page_size / 8) * 2 + 1 (prp1)

const size_t kMaxPRPPages = (page_size / 8) * 2 + 1;  // Dynamic based on page size
```

**For 4KB pages:**
- PRP entries per page: 4096 / 8 = 512 entries
- Max PRP list entries: 512 * 2 = 1024 entries
- Max data pages: 1024 + 1 = 1025 pages (~4MB)

### 4.3 PRP Building Functions

| Function | Location | Purpose |
|----------|----------|---------|
| `build_prps()` | `src/host/io/host_io_host_mem_impl.h:51` | Host memory PRPs |
| `build_prps()` | `src/common/memory/memory_pool.h:115` | Pool buffer PRPs |
| `build_prps_for_gpu()` | `src/cuda_gpu/io/cuda_io_gpu_mem.cpp:75` | GPU scatter-gather PRPs |
| `build_prps_for_gpu_ex()` | `src/cuda_gpu/io/cuda_io_gpu_mem.cpp:144` | GPU PRPs with explicit IOVA |
| `compute_runtime_prps()` | `src/host/io/host_io_host_mem_impl.h:86` | Runtime PRP computation |

### 4.4 Pool-level PRP Allocation

Location: `src/common/memory/memory_pool.h:197-263`

```cpp
// Calculate PRP list size based on buffer pages
const size_t prplist_bytes = (pages > 2) ? round_up((pages - 1) * sizeof(uint64_t), page_size) : 0;

// Each buffer chunk includes data + PRP list
const size_t chunk_size = buf_size + prplist_bytes;

// For each buffer in pool:
buf.prplist_host = prplist;           // Host pointer
buf.prplist_iova = prplist_iova;      // IOVA for NVMe
buf.prplist_bytes = prplist_bytes;    // Size
build_prps(buf.iova, buf.prplist_iova, buf.bytes, buf.prp1, buf.prp2);
```

---

## 5. Recommendations

### 5.1 High Priority - Replace Hardcoded Values

1. **`src/cuda_host/io/cuda_io_host_mem.cpp:21`**
   - Change `constexpr size_t kPage = 4096;` to use `nvme_get_page_size(device)`

2. **Memory alignment masks in `memory_types.h`**
   - Consider making alignment dynamic based on device page size

3. **Benchmark files with hardcoded I/O sizes**
   - Use environment variables or device query for page/LBA sizes

### 5.2 Medium Priority - Configuration

1. **Test constants** - Use `nvme_get_page_size()` and `nvme_get_lba_size()`
2. **Performance tests** - Read from environment or device capabilities

### 5.3 Low Priority - Acceptable Defaults

1. Default values in `NvmeDevice` struct (source of truth)
2. Test fixture defaults (512/4096 are standard values)
3. Documentation examples

---

## 6. Constants Summary Table

| Constant Name | Value | Location | Usage |
|---------------|-------|----------|-------|
| `kPage` | 4096 | Multiple test files | Page size constant |
| `CHUNK_SIZE` | 4096 | Performance tests | I/O operation size |
| `PAGE_SIZE` | 4096 | benchmark_constants.h | Alignment |
| `BUFFER_SIZE_4KB` | 4096 | benchmark_constants.h | Buffer allocation |
| `DEFAULT_CHUNK_SIZE` | 4096 | perf_test_helper.h | Default I/O size |
| `BLOCK_SIZE` | 4096 | gds_benchmark.cpp | GDS block size |
| `LBA_SIZE` | 512 | benchmark_constants.h | Logical block size |
| `lba_size_` | 512 | Various | Member variable default |
| `kPRPEntriesPerPage` | 512 | test_prp_edge_cases.cpp | PRP entries per 4KB page |
