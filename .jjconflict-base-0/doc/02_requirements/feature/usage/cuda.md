# cuda
*Source:* `test/feature/usage/cuda_spec.spl`

## Feature: CUDA Availability

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | checks CUDA availability | pass |
| 2 | reports device count | pass |

**Example:** checks CUDA availability
    Given val available = cuda_available()

**Example:** reports device count
    Given val count = cuda_device_count()

## Feature: CUDA Device Selection

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | sets and gets current device | pass |
| 2 | gets device info | pass |
| 3 | gets compute capability | pass |

**Example:** gets device info
    Given val info = cuda_device_info(0)

**Example:** gets compute capability
    Given val info = cuda_device_info(0)
    Given val (major, minor) = info.compute_capability

## Feature: CUDA Memory Operations

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | allocates CUDA memory | pass |
| 2 | performs memset | pass |
| 3 | copies host to device | pass |
| 4 | copies device to host | pass |
| 5 | copies device to device | pass |

**Example:** allocates CUDA memory
    Given val ptr = cuda_alloc(1024)
    Then  expect(ptr.size).to_equal(1024)

**Example:** performs memset
    Given val ptr = cuda_alloc(1024)

**Example:** copies host to device
    Given val ptr = cuda_alloc(16)
    Given val data: [u8] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]

**Example:** copies device to host
    Given val ptr = cuda_alloc(16)
    Given val src: [u8] = [10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 120, 130, 140, 150, 160]
    Given var dst: [u8] = []

**Example:** copies device to device
    Given val src = cuda_alloc(1024)
    Given val dst = cuda_alloc(1024)

## Feature: CUDA Kernel Compilation

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | compiles PTX module | pass |
| 2 | gets kernel function from module | pass |

**Example:** compiles PTX module
    Given val ptx = VECTOR_ADD_PTX
    Given val module = cuda_compile(ptx)

**Example:** gets kernel function from module
    Given val module = cuda_compile(VECTOR_ADD_PTX)
    Given val kfn = cuda_get_kernel(module, "vector_add")

## Feature: CUDA Streams

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates and destroys stream | pass |
| 2 | synchronizes stream | pass |

**Example:** creates and destroys stream
    Given val stream = cuda_stream_create()

**Example:** synchronizes stream
    Given val stream = cuda_stream_create()

## Feature: CUDA Error Handling

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | gets last error | pass |
| 2 | peeks at error without clearing | pass |

**Example:** gets last error
    Given val error_text = cuda_last_error()

**Example:** peeks at error without clearing
    Given val error_text = cuda_peek_error()

## Feature: CUDA Synchronization

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | synchronizes device | pass |
| 2 | creates gpu_cuda device wrapper | pass |

**Example:** creates gpu_cuda device wrapper
    Given val device = gpu_cuda(0)


