# CUDA Device Buffer Specification

> Purpose: Verify CUDA explicit device buffer transfers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CUDA Device Buffer Specification

Purpose: Verify CUDA explicit device buffer transfers.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | REQ-SCILIB-C-002, REQ-SCILIB-C-004, REQ-SCILIB-C-005, NFR-SCILIB-C-001, NFR-SCILIB-C-002 |
| Category | Other |
| Status | Active |
| Source | `test/feature/scilib/cuda_device_buffer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify CUDA explicit device buffer transfers.
Audience: QA and feature maintainers reading this spec suite.

## Scenarios

### CUDA explicit device buffer transfers

#### round-trips host i64 values through a device buffer when CUDA is available

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips host i64 values through a device buffer when CUDA is available
- round-trips host i64 values through a device buffer when CUDA is available
   - Expected: bytes equals `16`
   - Expected: false is true
   - Expected: out[0] equals `11`
   - Expected: out[1] equals `22`
   - Expected: false is true
   - Expected: buffer.free() equals `CUDA_SUCCESS`
   - Expected: false is true
   - Expected: buffer.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("round-trips host i64 values through a device buffer when CUDA is available")
step("round-trips host i64 values through a device buffer when CUDA is available")
# @req: REQ-SCILIB-C-002
# @req: REQ-SCILIB-C-004
# @req: REQ-SCILIB-C-005
val result = CudaBuffer.allocate(16)
if cuda_available():
    match result:
        case Ok(buffer):
            val copied = buffer.copy_from_i64_values([11, 22])
            match copied:
                case Ok(bytes):
                    expect(bytes).to_equal(16)
                case _:
                    expect(false).to_equal(true)
            val values = buffer.copy_to_i64_values(2)
            match values:
                case Ok(out):
                    expect(out[0]).to_equal(11)
                    expect(out[1]).to_equal(22)
                case _:
                    expect(false).to_equal(true)
            expect(buffer.free()).to_equal(CUDA_SUCCESS)
        case _:
            expect(false).to_equal(true)
else:
    match result:
        case Err(code):
            expect(code).to_be_less_than(0)
        case Ok(buffer):
            expect(buffer.free()).to_equal(CUDA_SUCCESS)
```

</details>

#### copies between device buffers without an implicit host fallback

- copies between device buffers without an implicit host fallback
- copies between device buffers without an implicit host fallback
   - Expected: src.copy_from_i64_values([7, 9]).unwrap() equals `16`
   - Expected: src.copy_to(dst, 16).unwrap() equals `16`
   - Expected: out[0] equals `7`
   - Expected: out[1] equals `9`
   - Expected: src.free() equals `CUDA_SUCCESS`
   - Expected: dst.free() equals `CUDA_SUCCESS`
   - Expected: false is true
   - Expected: false is true
   - Expected: buffer.free() equals `CUDA_SUCCESS`
   - Expected: buffer.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("copies between device buffers without an implicit host fallback")
step("copies between device buffers without an implicit host fallback")
val left = CudaBuffer.allocate(16)
val right = CudaBuffer.allocate(16)
if cuda_available():
    match left:
        case Ok(src):
            match right:
                case Ok(dst):
                    expect(src.copy_from_i64_values([7, 9]).unwrap()).to_equal(16)
                    expect(src.copy_to(dst, 16).unwrap()).to_equal(16)
                    val out = dst.copy_to_i64_values(2).unwrap()
                    expect(out[0]).to_equal(7)
                    expect(out[1]).to_equal(9)
                    expect(src.free()).to_equal(CUDA_SUCCESS)
                    expect(dst.free()).to_equal(CUDA_SUCCESS)
                case _:
                    expect(false).to_equal(true)
        case _:
            expect(false).to_equal(true)
else:
    match left:
        case Err(code):
            expect(code).to_be_less_than(0)
        case Ok(buffer):
            expect(buffer.free()).to_equal(CUDA_SUCCESS)
    match right:
        case Err(code):
            expect(code).to_be_less_than(0)
        case Ok(buffer):
            expect(buffer.free()).to_equal(CUDA_SUCCESS)
```

</details>

#### rejects invalid transfer sizes before backend execution

- rejects invalid transfer sizes before backend execution
- rejects invalid transfer sizes before backend execution
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects invalid transfer sizes before backend execution")
step("rejects invalid transfer sizes before backend execution")
val result = CudaBuffer(ptr: 1, size: 8).copy_from_i64_values([1, 2])
match result:
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        expect(false).to_equal(true)
```

</details>

### CUDA NDArray-owned storage

#### round-trips a Float64 host NDArray through CUDA-owned storage when available

- round-trips a Float64 host NDArray through CUDA-owned storage when available
- round-trips a Float64 host NDArray through CUDA-owned storage when available
   - Expected: device_array.shape equals `host.shape`
   - Expected: device_array.dtype equals `DType.F64`
   - Expected: device_array.device equals `Device.CUDA(index: 0)`
   - Expected: round_trip.shape equals `host.shape`
   - Expected: round_trip.get_f64_at([Index.new(0), Index.new(0)]) equals `Float64.new(1.5)`
   - Expected: round_trip.get_f64_at([Index.new(0), Index.new(1)]) equals `Float64.new(-2.25)`
   - Expected: round_trip.get_f64_at([Index.new(1), Index.new(0)]) equals `Float64.new(3.75)`
   - Expected: round_trip.get_f64_at([Index.new(1), Index.new(1)]) equals `Float64.new(4.5)`
   - Expected: device_array.free() equals `CUDA_SUCCESS`
   - Expected: false is true
   - Expected: device_array.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("round-trips a Float64 host NDArray through CUDA-owned storage when available")
step("round-trips a Float64 host NDArray through CUDA-owned storage when available")
val host = make_f64_array(
    [Float64.new(1.5), Float64.new(-2.25), Float64.new(3.75), Float64.new(4.5)],
    Shape.new([Index.new(2), Index.new(2)])
)
val result = CudaNDArray.from_f64_array(host, 0)
if cuda_available():
    match result:
        case Ok(device_array):
            expect(device_array.shape).to_equal(host.shape)
            expect(device_array.dtype).to_equal(DType.F64)
            expect(device_array.device).to_equal(Device.CUDA(index: 0))
            val round_trip = device_array.to_host_f64().unwrap()
            expect(round_trip.shape).to_equal(host.shape)
            expect(round_trip.get_f64_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(1.5))
            expect(round_trip.get_f64_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(-2.25))
            expect(round_trip.get_f64_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(3.75))
            expect(round_trip.get_f64_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(4.5))
            expect(device_array.free()).to_equal(CUDA_SUCCESS)
        case _:
            expect(false).to_equal(true)
else:
    match result:
        case Err(code):
            expect(code).to_be_less_than(0)
        case Ok(device_array):
            expect(device_array.free()).to_equal(CUDA_SUCCESS)
```

</details>

#### rejects non-Float64 host arrays before device allocation

- rejects non-Float64 host arrays before device allocation
- rejects non-Float64 host arrays before device allocation
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects non-Float64 host arrays before device allocation")
step("rejects non-Float64 host arrays before device allocation")
val host = make_i64_array([Int64.new(1), Int64.new(2)], Shape.new([Index.new(2)]))
val result = CudaNDArray.from_f64_array(host, 0)
match result:
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        expect(false).to_equal(true)
```

</details>

### CUDA NDArray explicit arithmetic

#### adds, subtracts, multiplies, and divides Float64 CUDA-owned arrays with device-side kernels

- adds, subtracts, multiplies, and divides Float64 CUDA-owned arrays with device-side kernels
- adds, subtracts, multiplies, and divides Float64 CUDA-owned arrays with device-side kernels
   - Expected: added.to_host_f64().unwrap().get_f64(Index.new(0)) equals `Float64.new(10.0)`
   - Expected: added.to_host_f64().unwrap().get_f64(Index.new(3)) equals `Float64.new(3.0)`
   - Expected: subbed.to_host_f64().unwrap().get_f64(Index.new(1)) equals `Float64.new(3.0)`
   - Expected: multiplied.to_host_f64().unwrap().get_f64(Index.new(2)) equals `Float64.new(16.0)`
   - Expected: divided.to_host_f64().unwrap().get_f64(Index.new(0)) equals `Float64.new(4.0)`
   - Expected: added.device equals `Device.CUDA(index: 0)`
   - Expected: added.free() equals `CUDA_SUCCESS`
   - Expected: subbed.free() equals `CUDA_SUCCESS`
   - Expected: multiplied.free() equals `CUDA_SUCCESS`
   - Expected: divided.free() equals `CUDA_SUCCESS`
   - Expected: left.free() equals `CUDA_SUCCESS`
   - Expected: right.free() equals `CUDA_SUCCESS`
   - Expected: false is true
   - Expected: false is true
   - Expected: left.free() equals `CUDA_SUCCESS`
   - Expected: right.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds, subtracts, multiplies, and divides Float64 CUDA-owned arrays with device-side kernels")
step("adds, subtracts, multiplies, and divides Float64 CUDA-owned arrays with device-side kernels")
val left_host = make_f64_array(
    [Float64.new(8.0), Float64.new(6.0), Float64.new(4.0), Float64.new(2.0)],
    Shape.new([Index.new(4)])
)
val right_host = make_f64_array(
    [Float64.new(2.0), Float64.new(3.0), Float64.new(4.0), Float64.new(1.0)],
    Shape.new([Index.new(4)])
)
val left_result = CudaNDArray.from_f64_array(left_host, 0)
val right_result = CudaNDArray.from_f64_array(right_host, 0)
if cuda_available():
    match left_result:
        case Ok(left):
            match right_result:
                case Ok(right):
                    val added = left.add_f64(right).unwrap()
                    val subbed = left.sub_f64(right).unwrap()
                    val multiplied = left.mul_f64(right).unwrap()
                    val divided = left.div_f64(right).unwrap()
                    expect(added.to_host_f64().unwrap().get_f64(Index.new(0))).to_equal(Float64.new(10.0))
                    expect(added.to_host_f64().unwrap().get_f64(Index.new(3))).to_equal(Float64.new(3.0))
                    expect(subbed.to_host_f64().unwrap().get_f64(Index.new(1))).to_equal(Float64.new(3.0))
                    expect(multiplied.to_host_f64().unwrap().get_f64(Index.new(2))).to_equal(Float64.new(16.0))
                    expect(divided.to_host_f64().unwrap().get_f64(Index.new(0))).to_equal(Float64.new(4.0))
                    expect(added.device).to_equal(Device.CUDA(index: 0))
                    expect(added.free()).to_equal(CUDA_SUCCESS)
                    expect(subbed.free()).to_equal(CUDA_SUCCESS)
                    expect(multiplied.free()).to_equal(CUDA_SUCCESS)
                    expect(divided.free()).to_equal(CUDA_SUCCESS)
                    expect(left.free()).to_equal(CUDA_SUCCESS)
                    expect(right.free()).to_equal(CUDA_SUCCESS)
                case _:
                    expect(false).to_equal(true)
        case _:
            expect(false).to_equal(true)
else:
    match left_result:
        case Err(code):
            expect(code).to_be_less_than(0)
        case Ok(left):
            expect(left.free()).to_equal(CUDA_SUCCESS)
    match right_result:
        case Err(code):
            expect(code).to_be_less_than(0)
        case Ok(right):
            expect(right.free()).to_equal(CUDA_SUCCESS)
```

</details>

#### rejects shape and device mismatches before CUDA arithmetic transfers

- rejects shape and device mismatches before CUDA arithmetic transfers
- rejects shape and device mismatches before CUDA arithmetic transfers
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: false is true
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects shape and device mismatches before CUDA arithmetic transfers")
step("rejects shape and device mismatches before CUDA arithmetic transfers")
val left = CudaNDArray(
    buffer: CudaBuffer(ptr: 1, size: 8),
    shape: Shape.new([Index.new(1)]),
    dtype: DType.F64,
    device: Device.CUDA(index: 0)
)
val shape_mismatch = CudaNDArray(
    buffer: CudaBuffer(ptr: 1, size: 16),
    shape: Shape.new([Index.new(2)]),
    dtype: DType.F64,
    device: Device.CUDA(index: 0)
)
val device_mismatch = CudaNDArray(
    buffer: CudaBuffer(ptr: 1, size: 8),
    shape: Shape.new([Index.new(1)]),
    dtype: DType.F64,
    device: Device.CUDA(index: 1)
)
match left.add_f64(shape_mismatch):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        expect(false).to_equal(true)
match left.add_f64(device_mismatch):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        expect(false).to_equal(true)
```

</details>

#### applies scalar Float64 arithmetic to CUDA-owned arrays

- applies scalar Float64 arithmetic to CUDA-owned arrays
- applies scalar Float64 arithmetic to CUDA-owned arrays
   - Expected: added_host.get_f64(Index.new(0)) equals `Float64.new(10.0)`
   - Expected: subbed_host.get_f64(Index.new(1)) equals `Float64.new(5.0)`
   - Expected: multiplied_host.get_f64(Index.new(2)) equals `Float64.new(12.0)`
   - Expected: divided_host.get_f64(Index.new(3)) equals `Float64.new(1.0)`
   - Expected: added.free() equals `CUDA_SUCCESS`
   - Expected: subbed.free() equals `CUDA_SUCCESS`
   - Expected: multiplied.free() equals `CUDA_SUCCESS`
   - Expected: divided.free() equals `CUDA_SUCCESS`
   - Expected: device_array.free() equals `CUDA_SUCCESS`
   - Expected: false is true
   - Expected: device_array.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("applies scalar Float64 arithmetic to CUDA-owned arrays")
step("applies scalar Float64 arithmetic to CUDA-owned arrays")
val host = make_f64_array(
    [Float64.new(8.0), Float64.new(6.0), Float64.new(4.0), Float64.new(2.0)],
    Shape.new([Index.new(4)])
)
val result = CudaNDArray.from_f64_array(host, 0)
if cuda_available():
    match result:
        case Ok(device_array):
            val added = device_array.add_scalar_f64(Float64.new(2.0)).unwrap()
            val subbed = device_array.sub_scalar_f64(Float64.new(1.0)).unwrap()
            val multiplied = device_array.mul_scalar_f64(Float64.new(3.0)).unwrap()
            val divided = device_array.div_scalar_f64(Float64.new(2.0)).unwrap()
            val added_host = added.to_host_f64().unwrap()
            val subbed_host = subbed.to_host_f64().unwrap()
            val multiplied_host = multiplied.to_host_f64().unwrap()
            val divided_host = divided.to_host_f64().unwrap()
            expect(added_host.get_f64(Index.new(0))).to_equal(Float64.new(10.0))
            expect(subbed_host.get_f64(Index.new(1))).to_equal(Float64.new(5.0))
            expect(multiplied_host.get_f64(Index.new(2))).to_equal(Float64.new(12.0))
            expect(divided_host.get_f64(Index.new(3))).to_equal(Float64.new(1.0))
            expect(added.free()).to_equal(CUDA_SUCCESS)
            expect(subbed.free()).to_equal(CUDA_SUCCESS)
            expect(multiplied.free()).to_equal(CUDA_SUCCESS)
            expect(divided.free()).to_equal(CUDA_SUCCESS)
            expect(device_array.free()).to_equal(CUDA_SUCCESS)
        case _:
            expect(false).to_equal(true)
else:
    match result:
        case Err(code):
            expect(code).to_be_less_than(0)
        case Ok(device_array):
            expect(device_array.free()).to_equal(CUDA_SUCCESS)
```

</details>

#### rejects scalar arithmetic for non-Float64 CUDA owners before backend execution

- rejects scalar arithmetic for non-Float64 CUDA owners before backend execution
- rejects scalar arithmetic for non-Float64 CUDA owners before backend execution
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects scalar arithmetic for non-Float64 CUDA owners before backend execution")
step("rejects scalar arithmetic for non-Float64 CUDA owners before backend execution")
val ints = CudaNDArray(
    buffer: CudaBuffer(ptr: 1, size: 16),
    shape: Shape.new([Index.new(2)]),
    dtype: DType.I64,
    device: Device.CUDA(index: 0)
)
match ints.add_scalar_f64(Float64.new(1.0)):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        expect(false).to_equal(true)
```

</details>

### CUDA NDArray explicit shape operations

#### reshapes, flattens, and transposes CUDA-owned Float64 arrays with device copies

- reshapes, flattens, and transposes CUDA-owned Float64 arrays with device copies
- reshapes, flattens, and transposes CUDA-owned Float64 arrays with device copies
   - Expected: reshaped_host.shape equals `Shape.new([Index.new(3), Index.new(2)])`
   - Expected: reshaped_host.get_f64_at([Index.new(0), Index.new(0)]) equals `Float64.new(1.0)`
   - Expected: reshaped_host.get_f64_at([Index.new(2), Index.new(1)]) equals `Float64.new(6.0)`
   - Expected: flattened_host.shape equals `Shape.new([Index.new(6)])`
   - Expected: flattened_host.get_f64(Index.new(4)) equals `Float64.new(5.0)`
   - Expected: transposed_host.shape equals `Shape.new([Index.new(3), Index.new(2)])`
   - Expected: transposed_host.get_f64_at([Index.new(0), Index.new(1)]) equals `Float64.new(4.0)`
   - Expected: transposed_host.get_f64_at([Index.new(2), Index.new(1)]) equals `Float64.new(6.0)`
   - Expected: reshaped.free() equals `CUDA_SUCCESS`
   - Expected: flattened.free() equals `CUDA_SUCCESS`
   - Expected: transposed.free() equals `CUDA_SUCCESS`
   - Expected: device_array.free() equals `CUDA_SUCCESS`
   - Expected: false is true
   - Expected: device_array.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reshapes, flattens, and transposes CUDA-owned Float64 arrays with device copies")
step("reshapes, flattens, and transposes CUDA-owned Float64 arrays with device copies")
val host = make_f64_array(
    [
        Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
        Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)
    ],
    Shape.new([Index.new(2), Index.new(3)])
)
val result = CudaNDArray.from_f64_array(host, 0)
if cuda_available():
    match result:
        case Ok(device_array):
            val reshaped = device_array.reshape_f64(Shape.new([Index.new(3), Index.new(2)])).unwrap()
            val flattened = device_array.flatten_f64().unwrap()
            val transposed = device_array.transpose_2d_f64().unwrap()
            val reshaped_host = reshaped.to_host_f64().unwrap()
            val flattened_host = flattened.to_host_f64().unwrap()
            val transposed_host = transposed.to_host_f64().unwrap()
            expect(reshaped_host.shape).to_equal(Shape.new([Index.new(3), Index.new(2)]))
            expect(reshaped_host.get_f64_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(1.0))
            expect(reshaped_host.get_f64_at([Index.new(2), Index.new(1)])).to_equal(Float64.new(6.0))
            expect(flattened_host.shape).to_equal(Shape.new([Index.new(6)]))
            expect(flattened_host.get_f64(Index.new(4))).to_equal(Float64.new(5.0))
            expect(transposed_host.shape).to_equal(Shape.new([Index.new(3), Index.new(2)]))
            expect(transposed_host.get_f64_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(4.0))
            expect(transposed_host.get_f64_at([Index.new(2), Index.new(1)])).to_equal(Float64.new(6.0))
            expect(reshaped.free()).to_equal(CUDA_SUCCESS)
            expect(flattened.free()).to_equal(CUDA_SUCCESS)
            expect(transposed.free()).to_equal(CUDA_SUCCESS)
            expect(device_array.free()).to_equal(CUDA_SUCCESS)
        case _:
            expect(false).to_equal(true)
else:
    match result:
        case Err(code):
            expect(code).to_be_less_than(0)
        case Ok(device_array):
            expect(device_array.free()).to_equal(CUDA_SUCCESS)
```

</details>

#### keeps empty CUDA-owned Float64 shape operations typed and allocation-free

- keeps empty CUDA-owned Float64 shape operations typed and allocation-free
- keeps empty CUDA-owned Float64 shape operations typed and allocation-free
   - Expected: device_array.buffer.ptr equals `0`
   - Expected: device_array.buffer.size equals `0`
   - Expected: flattened.shape equals `Shape.new([Index.new(0)])`
   - Expected: flattened.to_host_f64().unwrap().len().value equals `0`
   - Expected: flattened.free() equals `CUDA_SUCCESS`
   - Expected: false is true
   - Expected: transposed.shape equals `Shape.new([Index.new(3), Index.new(0)])`
   - Expected: transposed.to_host_f64().unwrap().len().value equals `0`
   - Expected: transposed.free() equals `CUDA_SUCCESS`
   - Expected: false is true
   - Expected: device_array.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("keeps empty CUDA-owned Float64 shape operations typed and allocation-free")
step("keeps empty CUDA-owned Float64 shape operations typed and allocation-free")
val device_array = CudaNDArray(
    buffer: CudaBuffer(ptr: 0, size: 0),
    shape: Shape.new([Index.new(0), Index.new(3)]),
    dtype: DType.F64,
    device: Device.CUDA(index: 0)
)
expect(device_array.buffer.ptr).to_equal(0)
expect(device_array.buffer.size).to_equal(0)
match device_array.flatten_f64():
    case Ok(flattened):
        expect(flattened.shape).to_equal(Shape.new([Index.new(0)]))
        expect(flattened.to_host_f64().unwrap().len().value).to_equal(0)
        expect(flattened.free()).to_equal(CUDA_SUCCESS)
    case _:
        expect(false).to_equal(true)
match device_array.transpose_2d_f64():
    case Ok(transposed):
        expect(transposed.shape).to_equal(Shape.new([Index.new(3), Index.new(0)]))
        expect(transposed.to_host_f64().unwrap().len().value).to_equal(0)
        expect(transposed.free()).to_equal(CUDA_SUCCESS)
    case _:
        expect(false).to_equal(true)
expect(device_array.free()).to_equal(CUDA_SUCCESS)
```

</details>

#### rejects invalid CUDA reshape and transpose requests before backend execution

- rejects invalid CUDA reshape and transpose requests before backend execution
- rejects invalid CUDA reshape and transpose requests before backend execution
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: false is true
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: false is true
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: false is true
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects invalid CUDA reshape and transpose requests before backend execution")
step("rejects invalid CUDA reshape and transpose requests before backend execution")
val vector = CudaNDArray(
    buffer: CudaBuffer(ptr: 1, size: 24),
    shape: Shape.new([Index.new(3)]),
    dtype: DType.F64,
    device: Device.CUDA(index: 0)
)
val matrix = CudaNDArray(
    buffer: CudaBuffer(ptr: 1, size: 32),
    shape: Shape.new([Index.new(2), Index.new(2)]),
    dtype: DType.I64,
    device: Device.CUDA(index: 0)
)
match vector.reshape_f64(Shape.new([Index.new(2), Index.new(2)])):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        expect(false).to_equal(true)
match vector.reshape_f64(Shape.new([Index.new(-3)])):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        expect(false).to_equal(true)
match vector.transpose_2d_f64():
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        expect(false).to_equal(true)
match matrix.reshape_f64(Shape.new([Index.new(4)])):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        expect(false).to_equal(true)
```

</details>

### CUDA NDArray explicit combine operations

#### concatenates and stacks one-dimensional CUDA-owned Float64 arrays with device copies

- concatenates and stacks one-dimensional CUDA-owned Float64 arrays with device copies
- concatenates and stacks one-dimensional CUDA-owned Float64 arrays with device copies
   - Expected: concatenated_host.shape equals `Shape.new([Index.new(4)])`
   - Expected: concatenated_host.get_f64(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: concatenated_host.get_f64(Index.new(3)) equals `Float64.new(4.0)`
   - Expected: stacked_host.shape equals `Shape.new([Index.new(2), Index.new(2)])`
   - Expected: stacked_host.get_f64_at([Index.new(0), Index.new(1)]) equals `Float64.new(2.0)`
   - Expected: stacked_host.get_f64_at([Index.new(1), Index.new(0)]) equals `Float64.new(3.0)`
   - Expected: concatenated.free() equals `CUDA_SUCCESS`
   - Expected: stacked.free() equals `CUDA_SUCCESS`
   - Expected: left.free() equals `CUDA_SUCCESS`
   - Expected: right.free() equals `CUDA_SUCCESS`
   - Expected: false is true
   - Expected: false is true
   - Expected: left.free() equals `CUDA_SUCCESS`
   - Expected: right.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("concatenates and stacks one-dimensional CUDA-owned Float64 arrays with device copies")
step("concatenates and stacks one-dimensional CUDA-owned Float64 arrays with device copies")
val left_host = make_f64_array(
    [Float64.new(1.0), Float64.new(2.0)],
    Shape.new([Index.new(2)])
)
val right_host = make_f64_array(
    [Float64.new(3.0), Float64.new(4.0)],
    Shape.new([Index.new(2)])
)
val left_result = CudaNDArray.from_f64_array(left_host, 0)
val right_result = CudaNDArray.from_f64_array(right_host, 0)
if cuda_available():
    match left_result:
        case Ok(left):
            match right_result:
                case Ok(right):
                    val concatenated = CudaNDArray.concatenate_1d_f64([left, right]).unwrap()
                    val stacked = CudaNDArray.stack_1d_f64([left, right]).unwrap()
                    val concatenated_host = concatenated.to_host_f64().unwrap()
                    val stacked_host = stacked.to_host_f64().unwrap()
                    expect(concatenated_host.shape).to_equal(Shape.new([Index.new(4)]))
                    expect(concatenated_host.get_f64(Index.new(0))).to_equal(Float64.new(1.0))
                    expect(concatenated_host.get_f64(Index.new(3))).to_equal(Float64.new(4.0))
                    expect(stacked_host.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
                    expect(stacked_host.get_f64_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(2.0))
                    expect(stacked_host.get_f64_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(3.0))
                    expect(concatenated.free()).to_equal(CUDA_SUCCESS)
                    expect(stacked.free()).to_equal(CUDA_SUCCESS)
                    expect(left.free()).to_equal(CUDA_SUCCESS)
                    expect(right.free()).to_equal(CUDA_SUCCESS)
                case _:
                    expect(false).to_equal(true)
        case _:
            expect(false).to_equal(true)
else:
    match left_result:
        case Err(code):
            expect(code).to_be_less_than(0)
        case Ok(left):
            expect(left.free()).to_equal(CUDA_SUCCESS)
    match right_result:
        case Err(code):
            expect(code).to_be_less_than(0)
        case Ok(right):
            expect(right.free()).to_equal(CUDA_SUCCESS)
```

</details>

#### rejects invalid CUDA concatenate and stack requests before backend execution

- rejects invalid CUDA concatenate and stack requests before backend execution
- rejects invalid CUDA concatenate and stack requests before backend execution
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: false is true
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: false is true
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: false is true
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects invalid CUDA concatenate and stack requests before backend execution")
step("rejects invalid CUDA concatenate and stack requests before backend execution")
val vector = CudaNDArray(
    buffer: CudaBuffer(ptr: 1, size: 16),
    shape: Shape.new([Index.new(2)]),
    dtype: DType.F64,
    device: Device.CUDA(index: 0)
)
val short = CudaNDArray(
    buffer: CudaBuffer(ptr: 1, size: 8),
    shape: Shape.new([Index.new(1)]),
    dtype: DType.F64,
    device: Device.CUDA(index: 0)
)
val matrix = CudaNDArray(
    buffer: CudaBuffer(ptr: 1, size: 32),
    shape: Shape.new([Index.new(2), Index.new(2)]),
    dtype: DType.F64,
    device: Device.CUDA(index: 0)
)
val other_device = CudaNDArray(
    buffer: CudaBuffer(ptr: 1, size: 16),
    shape: Shape.new([Index.new(2)]),
    dtype: DType.F64,
    device: Device.CUDA(index: 1)
)
match CudaNDArray.concatenate_1d_f64([]):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        expect(false).to_equal(true)
match CudaNDArray.concatenate_1d_f64([vector, matrix]):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        expect(false).to_equal(true)
match CudaNDArray.concatenate_1d_f64([vector, other_device]):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        expect(false).to_equal(true)
match CudaNDArray.stack_1d_f64([vector, short]):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        expect(false).to_equal(true)
```

</details>

### CUDA NDArray explicit reductions

#### computes device-side Float64 scalar reductions for CUDA-owned arrays

- computes device-side Float64 scalar reductions for CUDA-owned arrays
- computes device-side Float64 scalar reductions for CUDA-owned arrays
   - Expected: device_array.sum_f64().unwrap() equals `Float64.new(6.0)`
   - Expected: device_array.mean_f64().unwrap() equals `Float64.new(1.5)`
   - Expected: device_array.min_f64().unwrap() equals `Float64.new(-2.0)`
   - Expected: device_array.max_f64().unwrap() equals `Float64.new(4.0)`
   - Expected: device_array.free() equals `CUDA_SUCCESS`
   - Expected: false is true
   - Expected: device_array.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes device-side Float64 scalar reductions for CUDA-owned arrays")
step("computes device-side Float64 scalar reductions for CUDA-owned arrays")
val host = make_f64_array(
    [Float64.new(1.0), Float64.new(-2.0), Float64.new(3.0), Float64.new(4.0)],
    Shape.new([Index.new(4)])
)
val result = CudaNDArray.from_f64_array(host, 0)
if cuda_available():
    match result:
        case Ok(device_array):
            expect(device_array.sum_f64().unwrap()).to_equal(Float64.new(6.0))
            expect(device_array.mean_f64().unwrap()).to_equal(Float64.new(1.5))
            expect(device_array.min_f64().unwrap()).to_equal(Float64.new(-2.0))
            expect(device_array.max_f64().unwrap()).to_equal(Float64.new(4.0))
            expect(device_array.free()).to_equal(CUDA_SUCCESS)
        case _:
            expect(false).to_equal(true)
else:
    match result:
        case Err(code):
            expect(code).to_be_less_than(0)
        case Ok(device_array):
            expect(device_array.free()).to_equal(CUDA_SUCCESS)
```

</details>

#### rejects empty CUDA mean/min/max before transfer

- rejects empty CUDA mean/min/max before transfer
- rejects empty CUDA mean/min/max before transfer
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: false is true
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: false is true
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects empty CUDA mean/min/max before transfer")
step("rejects empty CUDA mean/min/max before transfer")
val empty = CudaNDArray(
    buffer: CudaBuffer(ptr: 1, size: 0),
    shape: Shape.new([Index.new(0)]),
    dtype: DType.F64,
    device: Device.CUDA(index: 0)
)
match empty.mean_f64():
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        expect(false).to_equal(true)
match empty.min_f64():
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        expect(false).to_equal(true)
match empty.max_f64():
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        expect(false).to_equal(true)
```

</details>

#### computes device-side Float64 axis sums and means for two-dimensional CUDA-owned arrays

- computes device-side Float64 axis sums and means for two-dimensional CUDA-owned arrays
- computes device-side Float64 axis sums and means for two-dimensional CUDA-owned arrays
   - Expected: axis0_host.shape equals `Shape.new([Index.new(3)])`
   - Expected: axis0_host.get_f64(Index.new(0)) equals `Float64.new(5.0)`
   - Expected: axis0_host.get_f64(Index.new(1)) equals `Float64.new(7.0)`
   - Expected: axis0_host.get_f64(Index.new(2)) equals `Float64.new(9.0)`
   - Expected: axis1_host.shape equals `Shape.new([Index.new(2)])`
   - Expected: axis1_host.get_f64(Index.new(0)) equals `Float64.new(6.0)`
   - Expected: axis1_host.get_f64(Index.new(1)) equals `Float64.new(15.0)`
   - Expected: axis_neg_host.get_f64(Index.new(1)) equals `Float64.new(15.0)`
   - Expected: mean0_host.get_f64(Index.new(0)) equals `Float64.new(2.5)`
   - Expected: mean0_host.get_f64(Index.new(2)) equals `Float64.new(4.5)`
   - Expected: mean1_host.get_f64(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: mean1_host.get_f64(Index.new(1)) equals `Float64.new(5.0)`
   - Expected: axis0.free() equals `CUDA_SUCCESS`
   - Expected: axis1.free() equals `CUDA_SUCCESS`
   - Expected: axis_neg.free() equals `CUDA_SUCCESS`
   - Expected: mean0.free() equals `CUDA_SUCCESS`
   - Expected: mean1.free() equals `CUDA_SUCCESS`
   - Expected: device_array.free() equals `CUDA_SUCCESS`
   - Expected: false is true
   - Expected: device_array.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes device-side Float64 axis sums and means for two-dimensional CUDA-owned arrays")
step("computes device-side Float64 axis sums and means for two-dimensional CUDA-owned arrays")
val host = make_f64_array(
    [
        Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
        Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)
    ],
    Shape.new([Index.new(2), Index.new(3)])
)
val result = CudaNDArray.from_f64_array(host, 0)
if cuda_available():
    match result:
        case Ok(device_array):
            val axis0 = device_array.sum_axis_f64(Axis.new(0)).unwrap()
            val axis1 = device_array.sum_axis_f64(Axis.new(1)).unwrap()
            val axis_neg = device_array.sum_axis_f64(Axis.new(-1)).unwrap()
            val mean0 = device_array.mean_axis_f64(Axis.new(0)).unwrap()
            val mean1 = device_array.mean_axis_f64(Axis.new(1)).unwrap()
            val axis0_host = axis0.to_host_f64().unwrap()
            val axis1_host = axis1.to_host_f64().unwrap()
            val axis_neg_host = axis_neg.to_host_f64().unwrap()
            val mean0_host = mean0.to_host_f64().unwrap()
            val mean1_host = mean1.to_host_f64().unwrap()
            expect(axis0_host.shape).to_equal(Shape.new([Index.new(3)]))
            expect(axis0_host.get_f64(Index.new(0))).to_equal(Float64.new(5.0))
            expect(axis0_host.get_f64(Index.new(1))).to_equal(Float64.new(7.0))
            expect(axis0_host.get_f64(Index.new(2))).to_equal(Float64.new(9.0))
            expect(axis1_host.shape).to_equal(Shape.new([Index.new(2)]))
            expect(axis1_host.get_f64(Index.new(0))).to_equal(Float64.new(6.0))
            expect(axis1_host.get_f64(Index.new(1))).to_equal(Float64.new(15.0))
            expect(axis_neg_host.get_f64(Index.new(1))).to_equal(Float64.new(15.0))
            expect(mean0_host.get_f64(Index.new(0))).to_equal(Float64.new(2.5))
            expect(mean0_host.get_f64(Index.new(2))).to_equal(Float64.new(4.5))
            expect(mean1_host.get_f64(Index.new(0))).to_equal(Float64.new(2.0))
            expect(mean1_host.get_f64(Index.new(1))).to_equal(Float64.new(5.0))
            expect(axis0.free()).to_equal(CUDA_SUCCESS)
            expect(axis1.free()).to_equal(CUDA_SUCCESS)
            expect(axis_neg.free()).to_equal(CUDA_SUCCESS)
            expect(mean0.free()).to_equal(CUDA_SUCCESS)
            expect(mean1.free()).to_equal(CUDA_SUCCESS)
            expect(device_array.free()).to_equal(CUDA_SUCCESS)
        case _:
            expect(false).to_equal(true)
else:
    match result:
        case Err(code):
            expect(code).to_be_less_than(0)
        case Ok(device_array):
            expect(device_array.free()).to_equal(CUDA_SUCCESS)
```

</details>

#### rejects invalid CUDA axis reductions before backend execution

- rejects invalid CUDA axis reductions before backend execution
- rejects invalid CUDA axis reductions before backend execution
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: false is true
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: false is true
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects invalid CUDA axis reductions before backend execution")
step("rejects invalid CUDA axis reductions before backend execution")
val vector = CudaNDArray(
    buffer: CudaBuffer(ptr: 1, size: 16),
    shape: Shape.new([Index.new(2)]),
    dtype: DType.F64,
    device: Device.CUDA(index: 0)
)
val matrix = CudaNDArray(
    buffer: CudaBuffer(ptr: 1, size: 32),
    shape: Shape.new([Index.new(2), Index.new(2)]),
    dtype: DType.F64,
    device: Device.CUDA(index: 0)
)
match vector.sum_axis_f64(Axis.new(0)):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        expect(false).to_equal(true)
match matrix.sum_axis_f64(Axis.new(2)):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        expect(false).to_equal(true)
match matrix.mean_axis_f64(Axis.new(2)):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        expect(false).to_equal(true)
```

</details>

### CUDA NDArray explicit slicing

#### slices one-dimensional and two-dimensional CUDA-owned Float64 arrays

- slices one-dimensional and two-dimensional CUDA-owned Float64 arrays
- slices one-dimensional and two-dimensional CUDA-owned Float64 arrays
   - Expected: contiguous_host_slice.shape equals `Shape.new([Index.new(2)])`
   - Expected: contiguous_host_slice.get_f64(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: contiguous_host_slice.get_f64(Index.new(1)) equals `Float64.new(3.0)`
   - Expected: strided_host_slice.shape equals `Shape.new([Index.new(2)])`
   - Expected: strided_host_slice.get_f64(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: strided_host_slice.get_f64(Index.new(1)) equals `Float64.new(4.0)`
   - Expected: negative_host_slice.shape equals `Shape.new([Index.new(2)])`
   - Expected: negative_host_slice.get_f64(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: negative_host_slice.get_f64(Index.new(1)) equals `Float64.new(3.0)`
   - Expected: negative_strided_host_slice.shape equals `Shape.new([Index.new(2)])`
   - Expected: negative_strided_host_slice.get_f64(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: negative_strided_host_slice.get_f64(Index.new(1)) equals `Float64.new(3.0)`
   - Expected: reverse_host_slice.shape equals `Shape.new([Index.new(3)])`
   - Expected: reverse_host_slice.get_f64(Index.new(0)) equals `Float64.new(4.0)`
   - Expected: reverse_host_slice.get_f64(Index.new(1)) equals `Float64.new(3.0)`
   - Expected: reverse_host_slice.get_f64(Index.new(2)) equals `Float64.new(2.0)`
   - Expected: matrix_host_slice.shape equals `Shape.new([Index.new(2), Index.new(2)])`
   - Expected: matrix_host_slice.get_f64_at([Index.new(0), Index.new(0)]) equals `Float64.new(2.0)`
   - Expected: matrix_host_slice.get_f64_at([Index.new(1), Index.new(1)]) equals `Float64.new(6.0)`
   - Expected: strided_matrix_host_slice.shape equals `Shape.new([Index.new(2), Index.new(2)])`
   - Expected: strided_matrix_host_slice.get_f64_at([Index.new(0), Index.new(0)]) equals `Float64.new(1.0)`
   - Expected: strided_matrix_host_slice.get_f64_at([Index.new(1), Index.new(1)]) equals `Float64.new(9.0)`
   - Expected: negative_matrix_host_slice.shape equals `Shape.new([Index.new(2), Index.new(2)])`
   - Expected: negative_matrix_host_slice.get_f64_at([Index.new(0), Index.new(0)]) equals `Float64.new(5.0)`
   - Expected: negative_matrix_host_slice.get_f64_at([Index.new(1), Index.new(1)]) equals `Float64.new(9.0)`
   - Expected: negative_strided_matrix_host_slice.shape equals `Shape.new([Index.new(2), Index.new(2)])`
   - Expected: negative_strided_matrix_host_slice.get_f64_at([Index.new(0), Index.new(0)]) equals `Float64.new(1.0)`
   - Expected: negative_strided_matrix_host_slice.get_f64_at([Index.new(1), Index.new(1)]) equals `Float64.new(9.0)`
   - Expected: reverse_matrix_host_slice.shape equals `Shape.new([Index.new(2), Index.new(2)])`
   - Expected: reverse_matrix_host_slice.get_f64_at([Index.new(0), Index.new(0)]) equals `Float64.new(9.0)`
   - Expected: reverse_matrix_host_slice.get_f64_at([Index.new(1), Index.new(1)]) equals `Float64.new(5.0)`
   - Expected: empty_host_slice.shape equals `Shape.new([Index.new(0)])`
   - Expected: empty_host_slice.len().value equals `0`
   - Expected: empty_row_host_slice.shape equals `Shape.new([Index.new(0), Index.new(2)])`
   - Expected: empty_row_host_slice.len().value equals `0`
   - Expected: empty_col_host_slice.shape equals `Shape.new([Index.new(2), Index.new(0)])`
   - Expected: empty_col_host_slice.len().value equals `0`
   - Expected: contiguous_vector_slice.free() equals `CUDA_SUCCESS`
   - Expected: strided_vector_slice.free() equals `CUDA_SUCCESS`
   - Expected: negative_vector_slice.free() equals `CUDA_SUCCESS`
   - Expected: negative_strided_vector_slice.free() equals `CUDA_SUCCESS`
   - Expected: reverse_vector_slice.free() equals `CUDA_SUCCESS`
   - Expected: matrix_slice.free() equals `CUDA_SUCCESS`
   - Expected: strided_matrix_slice.free() equals `CUDA_SUCCESS`
   - Expected: negative_matrix_slice.free() equals `CUDA_SUCCESS`
   - Expected: negative_strided_matrix_slice.free() equals `CUDA_SUCCESS`
   - Expected: reverse_matrix_slice.free() equals `CUDA_SUCCESS`
   - Expected: empty_vector_slice.free() equals `CUDA_SUCCESS`
   - Expected: empty_row_matrix_slice.free() equals `CUDA_SUCCESS`
   - Expected: empty_col_matrix_slice.free() equals `CUDA_SUCCESS`
   - Expected: vector.free() equals `CUDA_SUCCESS`
   - Expected: matrix.free() equals `CUDA_SUCCESS`
   - Expected: false is true
   - Expected: false is true
   - Expected: vector.free() equals `CUDA_SUCCESS`
   - Expected: matrix.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 136 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("slices one-dimensional and two-dimensional CUDA-owned Float64 arrays")
step("slices one-dimensional and two-dimensional CUDA-owned Float64 arrays")
val vector_host = make_f64_array(
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)],
    Shape.new([Index.new(4)])
)
val matrix_host = make_f64_array(
    [
        Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
        Float64.new(4.0), Float64.new(5.0), Float64.new(6.0),
        Float64.new(7.0), Float64.new(8.0), Float64.new(9.0)
    ],
    Shape.new([Index.new(3), Index.new(3)])
)
val vector_result = CudaNDArray.from_f64_array(vector_host, 0)
val matrix_result = CudaNDArray.from_f64_array(matrix_host, 0)
if cuda_available():
    match vector_result:
        case Ok(vector):
            match matrix_result:
                case Ok(matrix):
                    val contiguous_vector_slice = vector.slice_1d_f64(Slice.new(Index.new(1), Index.new(3), Index.new(1))).unwrap()
                    val strided_vector_slice = vector.slice_1d_f64(Slice.new(Index.new(1), Index.new(4), Index.new(2))).unwrap()
                    val negative_vector_slice = vector.slice_1d_f64(Slice.new(Index.new(-3), Index.new(-1), Index.new(1))).unwrap()
                    val negative_strided_vector_slice = vector.slice_1d_f64(Slice.new(Index.new(-4), Index.new(4), Index.new(2))).unwrap()
                    val reverse_vector_slice = vector.slice_1d_f64(Slice.new(Index.new(3), Index.new(0), Index.new(-1))).unwrap()
                    val matrix_slice = matrix.slice_2d_f64(
                        Slice.new(Index.new(0), Index.new(2), Index.new(1)),
                        Slice.new(Index.new(1), Index.new(3), Index.new(1))
                    ).unwrap()
                    val strided_matrix_slice = matrix.slice_2d_f64(
                        Slice.new(Index.new(0), Index.new(3), Index.new(2)),
                        Slice.new(Index.new(0), Index.new(3), Index.new(2))
                    ).unwrap()
                    val negative_matrix_slice = matrix.slice_2d_f64(
                        Slice.new(Index.new(-2), Index.new(3), Index.new(1)),
                        Slice.new(Index.new(-2), Index.new(3), Index.new(1))
                    ).unwrap()
                    val negative_strided_matrix_slice = matrix.slice_2d_f64(
                        Slice.new(Index.new(-3), Index.new(3), Index.new(2)),
                        Slice.new(Index.new(-3), Index.new(3), Index.new(2))
                    ).unwrap()
                    val reverse_matrix_slice = matrix.slice_2d_f64(
                        Slice.new(Index.new(2), Index.new(0), Index.new(-1)),
                        Slice.new(Index.new(2), Index.new(0), Index.new(-1))
                    ).unwrap()
                    val empty_vector_slice = vector.slice_1d_f64(Slice.new(Index.new(2), Index.new(2), Index.new(1))).unwrap()
                    val empty_row_matrix_slice = matrix.slice_2d_f64(
                        Slice.new(Index.new(1), Index.new(1), Index.new(1)),
                        Slice.new(Index.new(0), Index.new(2), Index.new(1))
                    ).unwrap()
                    val empty_col_matrix_slice = matrix.slice_2d_f64(
                        Slice.new(Index.new(0), Index.new(2), Index.new(1)),
                        Slice.new(Index.new(2), Index.new(2), Index.new(1))
                    ).unwrap()
                    val contiguous_host_slice = contiguous_vector_slice.to_host_f64().unwrap()
                    val strided_host_slice = strided_vector_slice.to_host_f64().unwrap()
                    val negative_host_slice = negative_vector_slice.to_host_f64().unwrap()
                    val negative_strided_host_slice = negative_strided_vector_slice.to_host_f64().unwrap()
                    val reverse_host_slice = reverse_vector_slice.to_host_f64().unwrap()
                    val matrix_host_slice = matrix_slice.to_host_f64().unwrap()
                    val strided_matrix_host_slice = strided_matrix_slice.to_host_f64().unwrap()
                    val negative_matrix_host_slice = negative_matrix_slice.to_host_f64().unwrap()
                    val negative_strided_matrix_host_slice = negative_strided_matrix_slice.to_host_f64().unwrap()
                    val reverse_matrix_host_slice = reverse_matrix_slice.to_host_f64().unwrap()
                    val empty_host_slice = empty_vector_slice.to_host_f64().unwrap()
                    val empty_row_host_slice = empty_row_matrix_slice.to_host_f64().unwrap()
                    val empty_col_host_slice = empty_col_matrix_slice.to_host_f64().unwrap()
                    expect(contiguous_host_slice.shape).to_equal(Shape.new([Index.new(2)]))
                    expect(contiguous_host_slice.get_f64(Index.new(0))).to_equal(Float64.new(2.0))
                    expect(contiguous_host_slice.get_f64(Index.new(1))).to_equal(Float64.new(3.0))
                    expect(strided_host_slice.shape).to_equal(Shape.new([Index.new(2)]))
                    expect(strided_host_slice.get_f64(Index.new(0))).to_equal(Float64.new(2.0))
                    expect(strided_host_slice.get_f64(Index.new(1))).to_equal(Float64.new(4.0))
                    expect(negative_host_slice.shape).to_equal(Shape.new([Index.new(2)]))
                    expect(negative_host_slice.get_f64(Index.new(0))).to_equal(Float64.new(2.0))
                    expect(negative_host_slice.get_f64(Index.new(1))).to_equal(Float64.new(3.0))
                    expect(negative_strided_host_slice.shape).to_equal(Shape.new([Index.new(2)]))
                    expect(negative_strided_host_slice.get_f64(Index.new(0))).to_equal(Float64.new(1.0))
                    expect(negative_strided_host_slice.get_f64(Index.new(1))).to_equal(Float64.new(3.0))
                    expect(reverse_host_slice.shape).to_equal(Shape.new([Index.new(3)]))
                    expect(reverse_host_slice.get_f64(Index.new(0))).to_equal(Float64.new(4.0))
                    expect(reverse_host_slice.get_f64(Index.new(1))).to_equal(Float64.new(3.0))
                    expect(reverse_host_slice.get_f64(Index.new(2))).to_equal(Float64.new(2.0))
                    expect(matrix_host_slice.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
                    expect(matrix_host_slice.get_f64_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(2.0))
                    expect(matrix_host_slice.get_f64_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(6.0))
                    expect(strided_matrix_host_slice.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
                    expect(strided_matrix_host_slice.get_f64_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(1.0))
                    expect(strided_matrix_host_slice.get_f64_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(9.0))
                    expect(negative_matrix_host_slice.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
                    expect(negative_matrix_host_slice.get_f64_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(5.0))
                    expect(negative_matrix_host_slice.get_f64_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(9.0))
                    expect(negative_strided_matrix_host_slice.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
                    expect(negative_strided_matrix_host_slice.get_f64_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(1.0))
                    expect(negative_strided_matrix_host_slice.get_f64_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(9.0))
                    expect(reverse_matrix_host_slice.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
                    expect(reverse_matrix_host_slice.get_f64_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(9.0))
                    expect(reverse_matrix_host_slice.get_f64_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(5.0))
                    expect(empty_host_slice.shape).to_equal(Shape.new([Index.new(0)]))
                    expect(empty_host_slice.len().value).to_equal(0)
                    expect(empty_row_host_slice.shape).to_equal(Shape.new([Index.new(0), Index.new(2)]))
                    expect(empty_row_host_slice.len().value).to_equal(0)
                    expect(empty_col_host_slice.shape).to_equal(Shape.new([Index.new(2), Index.new(0)]))
                    expect(empty_col_host_slice.len().value).to_equal(0)
                    expect(contiguous_vector_slice.free()).to_equal(CUDA_SUCCESS)
                    expect(strided_vector_slice.free()).to_equal(CUDA_SUCCESS)
                    expect(negative_vector_slice.free()).to_equal(CUDA_SUCCESS)
                    expect(negative_strided_vector_slice.free()).to_equal(CUDA_SUCCESS)
                    expect(reverse_vector_slice.free()).to_equal(CUDA_SUCCESS)
                    expect(matrix_slice.free()).to_equal(CUDA_SUCCESS)
                    expect(strided_matrix_slice.free()).to_equal(CUDA_SUCCESS)
                    expect(negative_matrix_slice.free()).to_equal(CUDA_SUCCESS)
                    expect(negative_strided_matrix_slice.free()).to_equal(CUDA_SUCCESS)
                    expect(reverse_matrix_slice.free()).to_equal(CUDA_SUCCESS)
                    expect(empty_vector_slice.free()).to_equal(CUDA_SUCCESS)
                    expect(empty_row_matrix_slice.free()).to_equal(CUDA_SUCCESS)
                    expect(empty_col_matrix_slice.free()).to_equal(CUDA_SUCCESS)
                    expect(vector.free()).to_equal(CUDA_SUCCESS)
                    expect(matrix.free()).to_equal(CUDA_SUCCESS)
                case _:
                    expect(false).to_equal(true)
        case _:
            expect(false).to_equal(true)
else:
    match vector_result:
        case Err(code):
            expect(code).to_be_less_than(0)
        case Ok(vector):
            expect(vector.free()).to_equal(CUDA_SUCCESS)
    match matrix_result:
        case Err(code):
            expect(code).to_be_less_than(0)
        case Ok(matrix):
            expect(matrix.free()).to_equal(CUDA_SUCCESS)
```

</details>

#### rejects invalid CUDA slice requests before transfer

- rejects invalid CUDA slice requests before transfer
- rejects invalid CUDA slice requests before transfer
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: false is true
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects invalid CUDA slice requests before transfer")
step("rejects invalid CUDA slice requests before transfer")
val vector = CudaNDArray(
    buffer: CudaBuffer(ptr: 1, size: 32),
    shape: Shape.new([Index.new(4)]),
    dtype: DType.F64,
    device: Device.CUDA(index: 0)
)
val matrix = CudaNDArray(
    buffer: CudaBuffer(ptr: 1, size: 32),
    shape: Shape.new([Index.new(2), Index.new(2)]),
    dtype: DType.F64,
    device: Device.CUDA(index: 0)
)
match vector.slice_1d_f64(Slice.new(Index.new(0), Index.new(4), Index.new(0))):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        expect(false).to_equal(true)
match matrix.slice_2d_f64(
    Slice.new(Index.new(0), Index.new(3), Index.new(1)),
    Slice.new(Index.new(0), Index.new(2), Index.new(1))
):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        expect(false).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-SCILIB-C-002`
- `REQ-SCILIB-C-004`
- `REQ-SCILIB-C-005`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ec0e8e91995808a49987a1fcf1c9e4fc0663cc9ec4e6e3a019362a32d8cf7914`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ec0e8e91995808a49987a1fcf1c9e4fc0663cc9ec4e6e3a019362a32d8cf7914`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ec0e8e91995808a49987a1fcf1c9e4fc0663cc9ec4e6e3a019362a32d8cf7914`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/scilib/cuda_device_buffer_spec.spl
mirror: doc/06_spec/feature/scilib/cuda_device_buffer_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/cuda_device_buffer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/cuda_device_buffer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/cuda_device_buffer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/scilib/cuda_device_buffer_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips host i64 values through a device buffer when CUDA is available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/cuda_device_buffer_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'copies between device buffers without an implicit host fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/cuda_device_buffer_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid transfer sizes before backend execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
