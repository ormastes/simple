# CUDA Device Buffer Specification

> Validates explicit CUDA device-buffer allocation and transfer helpers. The test

<!-- sdn-diagram:id=cuda_device_buffer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cuda_device_buffer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cuda_device_buffer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cuda_device_buffer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CUDA Device Buffer Specification

Validates explicit CUDA device-buffer allocation and transfer helpers. The test

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | REQ-SCILIB-C-002, REQ-SCILIB-C-004, REQ-SCILIB-C-005, NFR-SCILIB-C-001, NFR-SCILIB-C-002 |
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/scilib/cuda_device_buffer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates explicit CUDA device-buffer allocation and transfer helpers. The test
is availability-gated: CPU-only or non-CUDA builds must report typed unavailable
codes instead of failing scalar science-lib verification.

## Scenarios

### CUDA explicit device buffer transfers

#### round-trips host i64 values through a device buffer when CUDA is available

1. fail
   - Expected: out[0] equals `11`
   - Expected: out[1] equals `22`
2. fail
   - Expected: buffer.free() equals `CUDA_SUCCESS`
3. fail
   - Expected: buffer.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = CudaBuffer.allocate(16)
if cuda_available():
    match result:
        case Ok(buffer):
            val copied = buffer.copy_from_i64_values([11, 22])
            match copied:
                case Ok(bytes):
                    expect(bytes).to_equal(16)
                case _:
                    fail("unexpected scilib backend result branch")
            val values = buffer.copy_to_i64_values(2)
            match values:
                case Ok(out):
                    expect(out[0]).to_equal(11)
                    expect(out[1]).to_equal(22)
                case _:
                    fail("unexpected scilib backend result branch")
            expect(buffer.free()).to_equal(CUDA_SUCCESS)
        case _:
            fail("unexpected scilib backend result branch")
else:
    match result:
        case Err(code):
            expect(code).to_be_less_than(0)
        case Ok(buffer):
            expect(buffer.free()).to_equal(CUDA_SUCCESS)
```

</details>

#### copies between device buffers without an implicit host fallback

1. fail
2. fail
   - Expected: buffer.free() equals `CUDA_SUCCESS`
   - Expected: buffer.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
                    fail("unexpected scilib backend result branch")
        case _:
            fail("unexpected scilib backend result branch")
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

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = CudaBuffer(ptr: 1, size: 8).copy_from_i64_values([1, 2])
match result:
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        fail("unexpected scilib backend result branch")
```

</details>

### CUDA NDArray-owned storage

#### round-trips a Float64 host NDArray through CUDA-owned storage when available

1. [Float64 new
2. Shape new
   - Expected: device_array.shape equals `host.shape`
   - Expected: device_array.dtype equals `DType.F64`
   - Expected: device_array.device equals `Device.CUDA(index: 0)`
   - Expected: round_trip.shape equals `host.shape`
   - Expected: round_trip.get_f64_at([Index.new(0), Index.new(0)]) equals `Float64.new(1.5)`
   - Expected: round_trip.get_f64_at([Index.new(0), Index.new(1)]) equals `Float64.new(-2.25)`
   - Expected: round_trip.get_f64_at([Index.new(1), Index.new(0)]) equals `Float64.new(3.75)`
   - Expected: round_trip.get_f64_at([Index.new(1), Index.new(1)]) equals `Float64.new(4.5)`
   - Expected: device_array.free() equals `CUDA_SUCCESS`
3. fail
   - Expected: device_array.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
            fail("unexpected scilib backend result branch")
else:
    match result:
        case Err(code):
            expect(code).to_be_less_than(0)
        case Ok(device_array):
            expect(device_array.free()).to_equal(CUDA_SUCCESS)
```

</details>

#### rejects non-Float64 host arrays before device allocation

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host = make_i64_array([Int64.new(1), Int64.new(2)], Shape.new([Index.new(2)]))
val result = CudaNDArray.from_f64_array(host, 0)
match result:
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        fail("unexpected scilib backend result branch")
```

</details>

### CUDA NDArray explicit arithmetic

#### adds, subtracts, multiplies, and divides Float64 CUDA-owned arrays with device-side kernels

1. [Float64 new
2. Shape new
3. [Float64 new
4. Shape new
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
5. fail
6. fail
   - Expected: left.free() equals `CUDA_SUCCESS`
   - Expected: right.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
                    fail("unexpected scilib backend result branch")
        case _:
            fail("unexpected scilib backend result branch")
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

1. buffer: CudaBuffer
2. shape: Shape new
3. device: Device CUDA
4. buffer: CudaBuffer
5. shape: Shape new
6. device: Device CUDA
7. buffer: CudaBuffer
8. shape: Shape new
9. device: Device CUDA
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
10. fail
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
11. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
        fail("unexpected scilib backend result branch")
match left.add_f64(device_mismatch):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        fail("unexpected scilib backend result branch")
```

</details>

#### applies scalar Float64 arithmetic to CUDA-owned arrays

1. [Float64 new
2. Shape new
   - Expected: added_host.get_f64(Index.new(0)) equals `Float64.new(10.0)`
   - Expected: subbed_host.get_f64(Index.new(1)) equals `Float64.new(5.0)`
   - Expected: multiplied_host.get_f64(Index.new(2)) equals `Float64.new(12.0)`
   - Expected: divided_host.get_f64(Index.new(3)) equals `Float64.new(1.0)`
   - Expected: added.free() equals `CUDA_SUCCESS`
   - Expected: subbed.free() equals `CUDA_SUCCESS`
   - Expected: multiplied.free() equals `CUDA_SUCCESS`
   - Expected: divided.free() equals `CUDA_SUCCESS`
   - Expected: device_array.free() equals `CUDA_SUCCESS`
3. fail
   - Expected: device_array.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
            fail("unexpected scilib backend result branch")
else:
    match result:
        case Err(code):
            expect(code).to_be_less_than(0)
        case Ok(device_array):
            expect(device_array.free()).to_equal(CUDA_SUCCESS)
```

</details>

#### rejects scalar arithmetic for non-Float64 CUDA owners before backend execution

1. buffer: CudaBuffer
2. shape: Shape new
3. device: Device CUDA
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
4. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
        fail("unexpected scilib backend result branch")
```

</details>

### CUDA NDArray explicit shape operations

#### reshapes, flattens, and transposes CUDA-owned Float64 arrays with device copies

1. Float64 new
2. Float64 new
3. Shape new
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
4. fail
   - Expected: device_array.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
            fail("unexpected scilib backend result branch")
else:
    match result:
        case Err(code):
            expect(code).to_be_less_than(0)
        case Ok(device_array):
            expect(device_array.free()).to_equal(CUDA_SUCCESS)
```

</details>

#### keeps empty CUDA-owned Float64 shape operations typed and allocation-free

1. buffer: CudaBuffer
2. shape: Shape new
3. device: Device CUDA
   - Expected: device_array.buffer.ptr equals `0`
   - Expected: device_array.buffer.size equals `0`
   - Expected: flattened.shape equals `Shape.new([Index.new(0)])`
   - Expected: flattened.to_host_f64().unwrap().len().value equals `0`
   - Expected: flattened.free() equals `CUDA_SUCCESS`
4. fail
   - Expected: transposed.shape equals `Shape.new([Index.new(3), Index.new(0)])`
   - Expected: transposed.to_host_f64().unwrap().len().value equals `0`
   - Expected: transposed.free() equals `CUDA_SUCCESS`
5. fail
   - Expected: device_array.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
        fail("unexpected scilib backend result branch")
match device_array.transpose_2d_f64():
    case Ok(transposed):
        expect(transposed.shape).to_equal(Shape.new([Index.new(3), Index.new(0)]))
        expect(transposed.to_host_f64().unwrap().len().value).to_equal(0)
        expect(transposed.free()).to_equal(CUDA_SUCCESS)
    case _:
        fail("unexpected scilib backend result branch")
expect(device_array.free()).to_equal(CUDA_SUCCESS)
```

</details>

#### rejects invalid CUDA reshape and transpose requests before backend execution

1. buffer: CudaBuffer
2. shape: Shape new
3. device: Device CUDA
4. buffer: CudaBuffer
5. shape: Shape new
6. device: Device CUDA
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
7. fail
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
8. fail
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
9. fail
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
10. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
        fail("unexpected scilib backend result branch")
match vector.reshape_f64(Shape.new([Index.new(-3)])):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        fail("unexpected scilib backend result branch")
match vector.transpose_2d_f64():
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        fail("unexpected scilib backend result branch")
match matrix.reshape_f64(Shape.new([Index.new(4)])):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        fail("unexpected scilib backend result branch")
```

</details>

### CUDA NDArray explicit combine operations

#### concatenates and stacks one-dimensional CUDA-owned Float64 arrays with device copies

1. [Float64 new
2. Shape new
3. [Float64 new
4. Shape new
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
5. fail
6. fail
   - Expected: left.free() equals `CUDA_SUCCESS`
   - Expected: right.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
                    fail("unexpected scilib backend result branch")
        case _:
            fail("unexpected scilib backend result branch")
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

1. buffer: CudaBuffer
2. shape: Shape new
3. device: Device CUDA
4. buffer: CudaBuffer
5. shape: Shape new
6. device: Device CUDA
7. buffer: CudaBuffer
8. shape: Shape new
9. device: Device CUDA
10. buffer: CudaBuffer
11. shape: Shape new
12. device: Device CUDA
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
13. fail
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
14. fail
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
15. fail
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
16. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
        fail("unexpected scilib backend result branch")
match CudaNDArray.concatenate_1d_f64([vector, matrix]):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        fail("unexpected scilib backend result branch")
match CudaNDArray.concatenate_1d_f64([vector, other_device]):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        fail("unexpected scilib backend result branch")
match CudaNDArray.stack_1d_f64([vector, short]):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        fail("unexpected scilib backend result branch")
```

</details>

### CUDA NDArray explicit reductions

#### computes device-side Float64 scalar reductions for CUDA-owned arrays

1. [Float64 new
2. Shape new
   - Expected: device_array.sum_f64().unwrap() equals `Float64.new(6.0)`
   - Expected: device_array.mean_f64().unwrap() equals `Float64.new(1.5)`
   - Expected: device_array.min_f64().unwrap() equals `Float64.new(-2.0)`
   - Expected: device_array.max_f64().unwrap() equals `Float64.new(4.0)`
   - Expected: device_array.free() equals `CUDA_SUCCESS`
3. fail
   - Expected: device_array.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
            fail("unexpected scilib backend result branch")
else:
    match result:
        case Err(code):
            expect(code).to_be_less_than(0)
        case Ok(device_array):
            expect(device_array.free()).to_equal(CUDA_SUCCESS)
```

</details>

#### rejects empty CUDA mean/min/max before transfer

1. buffer: CudaBuffer
2. shape: Shape new
3. device: Device CUDA
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
4. fail
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
5. fail
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
6. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
        fail("unexpected scilib backend result branch")
match empty.min_f64():
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        fail("unexpected scilib backend result branch")
match empty.max_f64():
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        fail("unexpected scilib backend result branch")
```

</details>

#### computes device-side Float64 axis sums and means for two-dimensional CUDA-owned arrays

1. Float64 new
2. Float64 new
3. Shape new
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
4. fail
   - Expected: device_array.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
            fail("unexpected scilib backend result branch")
else:
    match result:
        case Err(code):
            expect(code).to_be_less_than(0)
        case Ok(device_array):
            expect(device_array.free()).to_equal(CUDA_SUCCESS)
```

</details>

#### rejects invalid CUDA axis reductions before backend execution

1. buffer: CudaBuffer
2. shape: Shape new
3. device: Device CUDA
4. buffer: CudaBuffer
5. shape: Shape new
6. device: Device CUDA
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
7. fail
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
8. fail
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
9. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
        fail("unexpected scilib backend result branch")
match matrix.sum_axis_f64(Axis.new(2)):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        fail("unexpected scilib backend result branch")
match matrix.mean_axis_f64(Axis.new(2)):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        fail("unexpected scilib backend result branch")
```

</details>

### CUDA NDArray explicit slicing

#### slices one-dimensional and two-dimensional CUDA-owned Float64 arrays

1. [Float64 new
2. Shape new
3. Float64 new
4. Float64 new
5. Float64 new
6. Shape new
7. Slice new
8. Slice new
9. Slice new
10. Slice new
11. Slice new
12. Slice new
13. Slice new
14. Slice new
15. Slice new
16. Slice new
17. Slice new
18. Slice new
19. Slice new
20. Slice new
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
21. fail
22. fail
   - Expected: vector.free() equals `CUDA_SUCCESS`
   - Expected: matrix.free() equals `CUDA_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 133 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
                    fail("unexpected scilib backend result branch")
        case _:
            fail("unexpected scilib backend result branch")
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

1. buffer: CudaBuffer
2. shape: Shape new
3. device: Device CUDA
4. buffer: CudaBuffer
5. shape: Shape new
6. device: Device CUDA
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
7. fail
8. Slice new
9. Slice new
   - Expected: code equals `CUDA_ERROR_INVALID_VALUE`
10. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
        fail("unexpected scilib backend result branch")
match matrix.slice_2d_f64(
    Slice.new(Index.new(0), Index.new(3), Index.new(1)),
    Slice.new(Index.new(0), Index.new(2), Index.new(1))
):
    case Err(code):
        expect(code).to_equal(CUDA_ERROR_INVALID_VALUE)
    case _:
        fail("unexpected scilib backend result branch")
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
