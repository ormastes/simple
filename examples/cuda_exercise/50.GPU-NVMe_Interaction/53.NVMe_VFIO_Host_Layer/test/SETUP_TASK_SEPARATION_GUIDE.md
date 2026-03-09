# Setup Task and Production Code Separation Guide

**Principle**: Setup task helpers MUST remain in test/helper. Only the core production functionality moves to src libraries.

## Current Correct Separations

### ✅ Doorbell Daemon (COMPLETED)

**Production Library** (`src/common/doorbell/doorbell_daemon.h`):
- `nvme::DoorbellDaemon` class - core daemon functionality
- Methods: `start()`, `stop()`, `ring_count()`, `wait_for_ring_count()`
- Pure production implementation without test dependencies

**Test Helper** (`test/helper/setup_helper.h`):
- `HostDoorbellDaemonTask` class - setup task for tests
- Manages daemon lifecycle within test framework
- Handles cleanup and resource management
- Integration with SetupHelper and SetupArgs

### ✅ Device Selection (COMPLETED)

**Production Library** (`src/common/device/device_detector.h`):
- `SystemFeatures` struct with device selection methods
- `DeviceRequirements` and `SelectedDevices` structs
- Pure device detection and selection logic

**Test Helper** (`test/helper/setup_helper.h`):
- Various setup tasks that USE device selection
- Test-specific device configuration
- No separate DeviceChooserTask needed (selection is direct)

## Future Migration Guidelines

### ✅ VFIO Safety (COMPLETED)

**Production Library** (`src/common/utils/vfio_safety.h`):
- `vfio::SafetyCheck` struct and `SafetyStatus` enum
- `check_binding_safety()` function - pure validation logic
- `get_block_devices_for_bdf()` and related utilities
- No side effects, only safety validation

**Test Helper** (`test/helper/vfio_utils.h`):
- `ensure_vfio_binding()` and `restore_original_driver()` - actual binding operations
- Uses production safety checks before attempting binds
- Integration with GTEST_SKIP for test management

### ✅ DBC Setup (COMPLETED)

**Production Library** (`src/common/doorbell/dbc_setup.h`):
- `nvme::ShadowDoorbellBuffer` struct
- `allocate_shadow_doorbell_buffer()` and `free_shadow_doorbell_buffer()`
- `calculate_dbc_buffer_size()` and `get_doorbell_offset()` utilities
- Pure allocation and management functions

**Test Helper** (`test/helper/setup_helper.h`):
- `DbcShadowBufferTask` class - setup task for tests
- Uses production allocation functions
- Manages cleanup and teardown for tests

### Pattern Utils (TO BE MIGRATED)

**Should Move to Library** (`src/common/utils/pattern_utils.h`):
- `fill_sequential()`, `fill_alternating()`, `fill_block_pattern()`, `fill_prime_pattern()`
- Pure data generation functions

**Should Stay in Test Helper**:
- Any PatternSetupTask if created
- Pattern verification functions that use test assertions
- Test-specific pattern configurations


### NvmeConfig (TO BE MIGRATED)

**Should Move to Library** (`src/common/utils/nvme_config.h`):
- `DeviceConfig` struct
- `from_env()` parsing function
- `getenv_or()` utility functions

**MUST Stay in Test Helper**:
- `NvmeDeviceTest` GTest fixture
- `NvmeSetupTask` and related setup tasks
- Test-specific environment variable defaults

## Key Principles

### What Goes to Production Library:
1. **Core functionality** - The actual implementation
2. **Data structures** - Config structs, result types
3. **Stateless utilities** - Pure functions without side effects
4. **Resource managers** - Classes that manage resources (like DoorbellDaemon)

### What Stays in Test Helper:
1. **Setup tasks** - All `*Task` classes inheriting from SetupTask
2. **Test fixtures** - GTest fixtures and test base classes
3. **Cleanup logic** - Test-specific resource cleanup
4. **Test utilities** - Assertion helpers and fixtures
5. **SetupHelper integration** - Anything that uses SetupArgs, SetupResult

## Implementation Checklist for Migration

When migrating a test helper to production:

- [ ] Identify core functionality vs setup task code
- [ ] Move only core functionality to src/
- [ ] Keep all `*Task` classes in test/helper/
- [ ] Ensure production code has no test framework dependencies
- [ ] Update `*Task` class to use the new production library
- [ ] Verify clean compilation of both library and tests
- [ ] Document the separation in this guide

## Benefits of This Approach

1. **Clean separation** - Production code is not polluted with test infrastructure
2. **Reusability** - Libraries can be used outside of test context
3. **Maintainability** - Clear boundaries between test and production code
4. **Flexibility** - Tests can have complex setup without affecting production API
5. **Safety** - Setup tasks can add test-specific safety checks and validations
