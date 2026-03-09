# Module 53 System Tests

System-level integration tests that exercise the complete I/O path with real NVMe hardware through VFIO.

## Overview

These tests validate the end-to-end functionality of Module 53's host I/O layer:
- **Device Access**: VFIO-based userspace NVMe access
- **Queue Management**: I/O submission and completion queues
- **Doorbell Modes**: MMIO doorbell register writes
- **Buffer Management**: Host memory buffer pools with VFIO DMA mapping
- **I/O Operations**: Real NVMe READ/WRITE commands
- **Error Handling**: Timeout and error status handling

## Prerequisites

### 1. Hardware Requirements
- NVMe SSD accessible via VFIO
- X86_64 system with IOMMU support
- At least one free namespace or safe test area on NVMe device

### 2. System Configuration

**Enable IOMMU** (add to kernel boot parameters):
```bash
# Intel systems
intel_iommu=on iommu=pt

# AMD systems
amd_iommu=on iommu=pt
```

**Bind NVMe device to vfio-pci**:
```bash
# Find your NVMe device BDF (Bus:Device.Function)
lspci | grep -i nvme
# Example output: 41:00.0 Non-Volatile memory controller: Samsung...

# Run the VFIO setup script
cd ../../../53.NVMe_VFIO_Host_Layer
sudo ./scripts/setup_vfio_test_env.sh
```

### 3. Environment Variables

Before running tests, set these environment variables:

```bash
# NVMe device PCI address (from lspci)
export NVME_BDF="0000:41:00.0"

# Namespace ID (usually 1)
export NVME_NSID="1"

# Logical block size (512 or 4096 bytes)
export NVME_LBA_SIZE="512"

# Starting LBA for test area (IMPORTANT: must be safe to overwrite!)
export NVME_SLBA="2000000"
```

⚠️ **WARNING**: Tests will **WRITE DATA** to the NVMe device starting at `NVME_SLBA`. Ensure this area does not contain important data!

### 4. Permissions

System tests require root privileges for VFIO operations:
```bash
sudo -E ./test_host_io_system
```

The `-E` flag preserves environment variables.

## Running Tests

### Run All System Tests
```bash
cd build/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/system_test
sudo -E ./test_host_io_system
```

### Run Specific Test
```bash
sudo -E ./test_host_io_system --gtest_filter="HostIoMmioSystemTest.SingleBlockRead"
```

### Run with Verbose Output
```bash
sudo -E ./test_host_io_system --gtest_verbose
```

### Run via CTest
```bash
cd build
sudo -E ctest -R test_host_io_system -V
```

## Test Coverage

### Test Binary: `test_host_io_system`

#### Suite: `HostIoMmioSystemTest`

| Test Name | Description | Coverage |
|-----------|-------------|----------|
| `DeviceInitialization` | Device open, queue setup, property queries | Device management APIs |
| `PoolCreationAndManagement` | Buffer pool lifecycle, acquire/release | Pool management, VFIO DMA mapping |
| `SingleBlockRead` | Single read operation with MMIO doorbell | Basic I/O path, completion polling |
| `WriteReadVerifySequential` | Write pattern → Read → Verify data integrity | Write path, pattern verification |
| `MultipleOutstandingCommands` | Concurrent I/O commands (queue depth test) | Multiple outstanding I/Os, CID tracking |
| `ErrorHandlingInvalidSLBA` | Invalid LBA error detection | Error handling, status codes |

#### Suite: `HostIoHelperSystemTest`

| Test Name | Description | Coverage |
|-----------|-------------|----------|
| `DeviceAndPoolInitialization` | Validates SetupHelper-produced resources | Confirms helper task outputs |
| `BufferManagement` | Acquire/release via helper-managed pool | Host pool ergonomics under helper |
| `SingleBlockRead` | READ command with helper-managed queues | MMIO path with helper setup |
| `WriteReadVerifyPattern` | Sequential pattern write/read cycle | Helper-based integrity validation |
| `MultipleOutstandingCommands` | Concurrent READ submissions | Helper-managed queue depth + CID tracking |

## Pattern Verification

Tests use multiple data patterns to validate correctness:

### Sequential Pattern
```cpp
data[i] = (base_offset + i) & 0xFF
```
Used for basic read/write verification.

### Alternating Pattern
```cpp
data[i] = (i % 2 == 0) ? 0xAA : 0x55
```
Detects byte-level corruption.

### Block Pattern
```cpp
// Each block starts with block number, then sequential pattern
block[0:3] = block_number
block[4:] = (block_number + offset) & 0xFF
```
Validates block alignment and ordering.

## Expected Output

Successful test run:
```
============================================================
Module 53: Host I/O System Tests (MMIO + SetupHelper)
============================================================

Environment:
  NVME_BDF:      0000:41:00.0
  NVME_NSID:     1
  NVME_LBA_SIZE: 512
  NVME_SLBA:     2000000

=== Test Configuration ===
  BDF:         0000:41:00.0
  NSID:        1
  LBA Size:    512 bytes
  Start LBA:   2000000
  SQ Depth:    16
  CQ Depth:    16
  Pool Size:   4 buffers
  Test Size:   4096 bytes (8 LBAs)
==========================

[==========] Running 11 tests from 2 test suites.
[----------] Global test environment set-up.
[----------] 6 tests from HostIoMmioSystemTest
[ RUN      ] HostIoMmioSystemTest.DeviceInitialization
✓ Device initialization verified
[       OK ] HostIoMmioSystemTest.DeviceInitialization (5 ms)
...
[----------] 6 tests from HostIoMmioSystemTest (234 ms total)
[----------] 5 tests from HostIoHelperSystemTest
[ RUN      ] HostIoHelperSystemTest.DeviceAndPoolInitialization
✓ Device and pool initialized successfully
[       OK ] HostIoHelperSystemTest.DeviceAndPoolInitialization (4 ms)
...
[----------] 5 tests from HostIoHelperSystemTest (210 ms total)
[==========] 11 tests from 2 test suites ran. (444 ms total)
[  PASSED  ] 11 tests.

============================================================
Module 53 Host I/O System Tests Complete
============================================================
```

## Troubleshooting

### "Failed to open NVMe device"
- Check VFIO bindings: `ls /sys/bus/pci/drivers/vfio-pci/`
- Verify IOMMU is enabled: `dmesg | grep -i iommu`
- Run setup script: `sudo ./scripts/setup_vfio_test_env.sh`

### "Test environment not configured"
- Ensure all environment variables are set
- Use `sudo -E` to preserve environment

### "Permission denied"
- System tests require root: `sudo -E ./test_host_io_system`

### "Completion timeout"
- Device may be busy or locked by another process
- Check: `sudo lsof /dev/nvme*`
- Increase timeout in test code if device is slow

### "Pattern verification failed"
- Data corruption detected
- Check IOVA mapping is correct
- Verify SLBA is within device capacity
- Ensure no other process is accessing the same LBAs

## Adding New System Tests

Create a new test in `test_host_io_system.cpp`:

```cpp
TEST_F(HostIoMmioSystemTest, YourNewTest) {
    printf("=== Test: YourNewTest ===\n");

    // Your test code here

    printf("✓ Test passed\n\n");
}
```

Follow the existing pattern:
1. Use `HostIoMmioSystemTest` fixture for automatic device setup
2. Create pools with `host_pool_create()`
3. Use template API for compile-time optimization: `host_submit<CMD_*, DOORBELL_*>()`
4. Always check completion status
5. Verify data patterns when possible
6. Clean up resources

## Performance Benchmarking

For performance testing, use the benchmarks in `../../benchmarks/` instead. System tests focus on correctness, not performance.

## See Also

- [Module 53 README](../../README.md) - Architecture overview
- [VFIO Setup Script](../../scripts/setup_vfio_test_env.sh) - Device binding automation
- [Device Info Demo](../device_info_demo.cpp) - Device detection and capabilities
- [Integration Tests](../backup/integration/) - Legacy integration tests
