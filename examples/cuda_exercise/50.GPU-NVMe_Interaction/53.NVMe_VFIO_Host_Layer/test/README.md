# Module 53 Test Suite

This directory contains the comprehensive test suite for Module 53 (NVMe VFIO Host Layer) and Module 54 (CUDA Host Memory).

## Directory Structure

```
test/
├── README.md           - This file
├── CMakeLists.txt      - Test build configuration
├── unit/               - Unit tests (MANDATORY from Module 16+)
│   ├── common/         - Utility and helper function tests
│   ├── cuda_host/      - CUDA host memory tests (Module 54)
│   ├── host/           - Host-side I/O implementation tests
│   ├── part_specific/  - NVMe VFIO specific tests
│   └── queue/          - Queue factory and management tests
├── helper/             - Test helper libraries
│   ├── nvme_test_helper.h       - Common test utilities
│   ├── nvme_test_file_utils.*   - File LBA utilities
│   ├── device_chooser.*         - Intelligent device selection
│   ├── setup_helper.*           - Task-based test setup system
│   └── host_doorbell_daemon.*   - Doorbell daemon for testing
├── helper_test/        - Tests for helper utilities
├── system_test/        - System-level integration tests (requires VFIO hardware)
└── backup/             - Original test backups (for reference)
```

## Test Categories

### Unit Tests (test/unit/)

**Common Tests** (3 tests)
- `test_utility_functions_53` - Utility function validation
- `test_memory_buffer_utils_53` - Memory buffer utilities
- `test_doorbell_strategies_53` - Doorbell strategy patterns

**Host Tests** (3 tests)
- `test_host_io_host_mem_53` - Host memory I/O operations
- `test_prp_edge_cases_53` - PRP list edge cases (⚠️ needs API update)
- `test_template_combinations_53` - Template API combinations

**Part-Specific Tests** (4 tests)
- `test_nvme_vio_host_53` - NVMe VFIO host interface
- `test_nvme_page_size_53` - NVMe page size handling (⚠️ needs API update)
- `test_doorbell_support_53` - Doorbell support detection (⚠️ needs API update)
- `test_nvme_vio_host_buffer_53` - NVMe VFIO buffer pools

**Queue Tests** (1 test)
- `test_factory_methods_53` - Queue factory methods (⚠️ needs API update)

**CUDA Host Tests** (2 tests - Module 54 functionality)
- `test_cuda_io_host_mem_53` - CUDA host-pinned memory allocation
- `test_nvme_vio_cuda_host_buffer_53` - CUDA host buffer pools

### System Tests (test/system_test/)

**Module 53 Tests**
- `test_host_io_system` - Combined MMIO + SetupHelper host I/O flows
- `test_host_daemon_doorbell` - Host daemon doorbell mode
- `test_shadow_doorbell` - Shadow doorbell mode
- `test_host_dbc_daemon` - Host DBC daemon mode
- `test_mode_comparison_harness` - Multi-mode comparison framework

**Module 54 Tests**
- `test_cuda_host_io_system` - CUDA host-pinned memory integration with NVMe
- `test_gpu_queue_gpu_buffer` - GPU queue with GPU buffer (preview of Module 56)

### Helper Tests (test/helper_test/)

- `device_chooser_test` - Device selection logic tests
- `test_setup_tasks` - Hardware tests for all 14 setup tasks

## Build Status

### ✅ Successfully Building (8/13 unit tests)

All common, most host, part-specific, and CUDA host tests compile successfully.

### ⚠️ Needs API Updates (5/13 unit tests)

The following tests use outdated `nvme_pool_*` API instead of current `host_pool_*`:
- `test_prp_edge_cases_53`
- `test_nvme_page_size_53`
- `test_doorbell_support_53`
- `test_factory_methods_53`
- `test_nvme_vio_cuda_host_buffer_53`

**Fix**: Replace `nvme_pool_create/acquire/release/destroy` with `host_pool_*` equivalents.

## Running Tests

### Prerequisites

```bash
# Setup VFIO environment
cd ../scripts
sudo ./setup_vfio.sh

# Configure environment variables
export NVME_BDF="0000:41:00.0"      # Your NVMe device BDF
export NVME_NSID="1"                # Namespace ID
export NVME_LBA_SIZE="512"          # LBA size in bytes
export NVME_SLBA="2000000"          # Safe starting LBA
```

### Run Unit Tests

```bash
# From build directory
cd build/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/unit

# Run all unit tests
ctest -R "53$"

# Run specific category
./test_utility_functions_53
./test_cuda_io_host_mem_53
```

### Run System Tests

```bash
# Bind device to vfio-pci (if sudo configured)
sudo /usr/local/sbin/vfio-bind.sh $NVME_BDF

# Run system test
cd build/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/system_test
sudo -E ./test_host_io_system

# Restore device when done
sudo /usr/local/sbin/vfio-unbind.sh $NVME_BDF
```

## Test Helper Libraries

### nvme_test_helper

Common utilities for NVMe device tests:
- Environment variable parsing
- Device detection and setup
- Test fixtures for hardware tests

### device_chooser

Intelligent device selection based on features:
- PCIe/NVMe capability detection
- GPU P2P support detection
- Automatic best device selection

### setup_helper

Task-based test setup system with 14 tasks:
1. VFIO driver binding
2. Host queue creation
3. CUDA host memory setup
4. GPU memory P2P mapping
5-14. Various queue and buffer configurations

See `helper/README.md` for detailed helper documentation.

## Module Integration

### Module 54 Integration

Module 54 (CUDA Host Memory) is fully integrated into Module 53. All Module 54 tests are located in:
- **Unit tests**: `test/unit/cuda_host/`
- **System tests**: `test/system_test/test_cuda_host_io_system.cpp`

Module 54's `system_test/` directory is a symlink to this test directory.

### Module 55/56/57 Independence

Modules 55, 56, 57 maintain their own specialized tests:
- **Module 55**: GPU memory tests (independent)
- **Module 56**: GPU queue tests (references Module 55 via symlinks)
- **Module 57**: Performance benchmarks (independent)

## Contributing

When adding new unit tests:
1. Place in appropriate subdirectory (common/, host/, cuda_host/, part_specific/, queue/)
2. Follow naming convention: `test_<component>_53.cpp`
3. Use `configure_cpp_test_target()` macro in CMakeLists.txt
4. Add to `test/unit/CMakeLists.txt`
5. Include profiling targets via `add_profiling_targets()`

## References

- CLAUDE.md: Documentation format guide (requires unit tests from Module 16+)
- Module 53 README: `../README.md`
- Module 54 README: `../../54.CUDA_Host_Memory/README.md`
