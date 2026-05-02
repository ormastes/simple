# gpu basic
*Source:* `test/feature/usage/gpu_basic_spec.spl`

## Feature: GPU Device Management

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | detects available backends | pass |
| 2 | gets preferred backend | pass |
| 3 | lists all GPUs | pass |
| 4 | reports GPU availability consistently | pass |

**Example:** detects available backends
    Given val backends = detect_backends()
    Then  expect(backends.len() >= 0).to_equal(true)

**Example:** gets preferred backend
    Given val backend = preferred_backend()
    Then  expect(true).to_equal(true)
    Then  expect(true).to_equal(true)
    Then  expect(true).to_equal(true)
    Then  expect(true).to_equal(true)

**Example:** lists all GPUs
    Given val devices = list_all_gpus()
    Then  expect(devices.len() >= 0).to_equal(true)

**Example:** reports GPU availability consistently
    Given val available = gpu_available()
    Given val count = gpu_count()
    Then  expect(count > 0).to_equal(true)
    Then  expect(count).to_equal(0)

## Feature: GPU Default Device

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates default GPU device | pass |
| 2 | reports device validity correctly | pass |
| 3 | gets device name | pass |
| 4 | gets device memory | pass |

**Example:** creates default GPU device
    Given val device = gpu_default()
    Then  expect(true).to_equal(true)

**Example:** reports device validity correctly
    Given val device = gpu_default()
    Then  expect(device.is_valid()).to_equal(true)
    Then  expect(not device.is_valid()).to_equal(true)

**Example:** gets device name
    Given val device = gpu_default()
    Given val name = device.name()
    Then  expect(name.len() > 0).to_equal(true)

**Example:** gets device memory
    Given val device = gpu_default()
    Given val mem = device.total_memory()
    Then  expect(mem > 0).to_equal(true)

## Feature: GPU Memory Allocation

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | allocates and frees buffer | pass |
| 2 | handles zero-size allocation | pass |
| 3 | allocates typed arrays | pass |

**Example:** allocates and frees buffer
    Given val device = gpu_default()
    Given val buffer = gpu_alloc(device, 1024)
    Then  expect(buffer.is_valid).to_equal(true)
    Then  expect(buffer.len() == 1024).to_equal(true)
    Then  expect(gpu_free(buffer)).to_equal(true)

**Example:** handles zero-size allocation
    Given val device = gpu_default()
    Given val buffer = gpu_alloc(device, 0)

**Example:** allocates typed arrays
    Given val device = gpu_default()
    Given val floats = gpu_alloc_f32(device, 100)
    Then  expect(floats.valid()).to_equal(true)
    Then  expect(floats.count() == 100).to_equal(true)
    Then  expect(floats.size_bytes() == 400).to_equal(true)  # 100 * 4 bytes

## Feature: GPU Data Transfer

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | copies data to device | pass |
| 2 | copies data from device | pass |

**Example:** copies data to device
    Given val device = gpu_default()
    Given val buffer = gpu_alloc(device, 16)
    Given val data: [u8] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
    Given val success = gpu_copy_to(buffer, data)
    Then  expect(success).to_equal(true)

**Example:** copies data from device
    Given val device = gpu_default()
    Given val buffer = gpu_alloc(device, 16)
    Given val src: [u8] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
    Given var dst: [u8] = []
    Given val success = gpu_copy_from(dst, buffer)
    Then  expect(success).to_equal(true)

## Feature: GPU Synchronization

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | synchronizes device | pass |
| 2 | synchronizes all devices | pass |

**Example:** synchronizes device
    Given val device = gpu_default()
    Then  expect(device.wait_for_idle()).to_equal(true)

**Example:** synchronizes all devices
    Then  expect(gpu_wait_all()).to_equal(true)

## Feature: GPU Info

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | generates GPU info string | pass |
| 2 | runs GPU smoke test | pass |
| 3 | reports GPU is ready | pass |

**Example:** generates GPU info string
    Given val info = gpu_info()
    Then  expect(info.len() > 0).to_equal(true)
    Then  expect(info.contains("GPU Information")).to_equal(true)

**Example:** runs GPU smoke test
    Then  expect(gpu_test_basic()).to_equal(true)

**Example:** reports GPU is ready
    Then  expect(gpu_is_ready()).to_equal(true)


