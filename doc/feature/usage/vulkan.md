# vulkan
*Source:* `test/feature/usage/vulkan_spec.spl`

## Feature: Vulkan Availability

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | checks Vulkan availability | pass |

**Example:** checks Vulkan availability
    Given val available = vulkan_available()

## Feature: Vulkan Initialization

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | initializes Vulkan | pass |
| 2 | reports device count | pass |
| 3 | shuts down cleanly | pass |

**Example:** reports device count
    Given val count = vulkan_device_count()

## Feature: Vulkan Device Selection

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | selects device | pass |
| 2 | gets device info | pass |
| 3 | reports device type | pass |
| 4 | gets API version | pass |

**Example:** gets device info
    Given val info = vulkan_device_info(0)

**Example:** reports device type
    Given val info = vulkan_device_info(0)
    Then  expect(info.device_type == VulkanDeviceType.Discrete or info.device_type == VulkanDeviceType.Integrated or info.device_type == VulkanDeviceType.Virtual or info.device_type == VulkanDeviceType.CpuOnly or info.device_type).to_equal(VulkanDeviceType.Unknown)

**Example:** gets API version
    Given val info = vulkan_device_info(0)
    Given val (major, minor, patch) = info.api_version

## Feature: Vulkan Buffer Operations

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | allocates storage buffer | pass |
| 2 | allocates different buffer types | pass |
| 3 | copies data to buffer | pass |
| 4 | copies data from buffer | pass |
| 5 | copies between buffers | pass |

**Example:** allocates storage buffer
    Given val buf = vulkan_alloc_storage(1024)
    Then  expect(buf.size).to_equal(1024)

**Example:** allocates different buffer types
    Given val storage = vulkan_alloc_buffer(1024, VulkanBufferUsage.Storage)

**Example:** copies data to buffer
    Given val buf = vulkan_alloc_storage(16)
    Given val data: [u8] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]

**Example:** copies data from buffer
    Given val buf = vulkan_alloc_storage(16)
    Given val src: [u8] = [10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 120, 130, 140, 150, 160]
    Given var dst: [u8] = []

**Example:** copies between buffers
    Given val src = vulkan_alloc_storage(1024)
    Given val dst = vulkan_alloc_storage(1024)

## Feature: Vulkan Shader Compilation

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | compiles GLSL compute shader | pass |
| 2 | creates compute pipeline | pass |

**Example:** compiles GLSL compute shader
    Given val shader = vulkan_compile_glsl(VECTOR_ADD_GLSL)

**Example:** creates compute pipeline
    Given val shader = vulkan_compile_glsl(VECTOR_ADD_GLSL)
    Given val pipe = vulkan_create_pipeline(shader, "main")

## Feature: Vulkan Descriptor Sets

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates descriptor set | pass |
| 2 | binds buffers to descriptors | pass |

**Example:** creates descriptor set
    Given val shader = vulkan_compile_glsl(VECTOR_ADD_GLSL)
    Given val pipe = vulkan_create_pipeline(shader, "main")
    Given val descriptors = vulkan_create_descriptors(pipe)

**Example:** binds buffers to descriptors
    Given val shader = vulkan_compile_glsl(VECTOR_ADD_GLSL)
    Given val pipe = vulkan_create_pipeline(shader, "main")
    Given val descriptors = vulkan_create_descriptors(pipe)
    Given val buf = vulkan_alloc_storage(1024)

## Feature: Vulkan Command Execution

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | records and submits commands | pass |
| 2 | waits for device idle | pass |

**Example:** records and submits commands
    Given val cmd = vulkan_begin_compute()

## Feature: Vulkan Error Handling

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | gets last error message | pass |

**Example:** gets last error message
    Given val error_text = vulkan_last_error()

## Feature: Vulkan GPU Wrapper

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates gpu_vulkan device wrapper | pass |
| 2 | synchronizes via wrapper | pass |

**Example:** creates gpu_vulkan device wrapper
    Given val device = gpu_vulkan(0)

**Example:** synchronizes via wrapper
    Given val device = gpu_vulkan(0)


