# Tensor Broadcast Specification

> <details>

<!-- sdn-diagram:id=tensor_broadcast_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tensor_broadcast_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tensor_broadcast_spec -> std
tensor_broadcast_spec -> std_lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tensor_broadcast_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 39 | 39 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tensor Broadcast Specification

## Scenarios

#### Compute strides for 1D shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a 1D shape [5]"
val shape = [5]
# When "computing strides"
val strides = compute_strides(shape)
# Then "strides should be [1]"
expect(strides).to_equal([1])
```

</details>

#### Compute strides for 2D shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a 2D shape [3, 4]"
val shape = [3, 4]
# When "computing strides"
val strides = compute_strides(shape)
# Then "strides should be [4, 1]"
expect(strides).to_equal([4, 1])
```

</details>

#### Compute strides for 3D shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a 3D shape [2, 3, 4]"
val shape = [2, 3, 4]
# When "computing strides"
val strides = compute_strides(shape)
# Then "strides should be [12, 4, 1]"
expect(strides).to_equal([12, 4, 1])
```

</details>

#### Compute strides for empty shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an empty shape"
val shape = []
# When "computing strides"
val strides = compute_strides(shape)
# Then "strides should be empty"
expect(strides.length()).to_equal(0)
```

</details>

#### Get dimension within bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a shape [3, 4, 5] and max_len 3"
val shape = [3, 4, 5]
# When "getting dimension at index 2"
val dim = get_dim_aligned(shape, 2, max_len: 3)
# Then "it should return 5"
expect(dim).to_equal(5)
```

</details>

#### Get dimension with left padding

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a shape [4, 5] and max_len 3"
val shape = [4, 5]
# When "getting dimension at index 0 (left pad)"
val dim = get_dim_aligned(shape, 0, max_len: 3)
# Then "it should return 1 (padding)"
expect(dim).to_equal(1)
```

</details>

#### Equal dimensions are compatible

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "two equal dimensions"
val a = 5
val b = 5
# When "checking compatibility"
val compat = dims_compatible(a, b)
# Then "they should be compatible"
expect(compat).to_equal(true)
```

</details>

#### Dimension 1 is compatible with any

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "dimension 1 and dimension 5"
val a = 1
val b = 5
# When "checking compatibility"
val compat = dims_compatible(a, b)
# Then "they should be compatible"
expect(compat).to_equal(true)
```

</details>

#### Incompatible different dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "dimensions 3 and 5"
val a = 3
val b = 5
# When "checking compatibility"
val compat = dims_compatible(a, b)
# Then "they should not be compatible"
expect(compat).to_equal(false)
```

</details>

#### Broadcast equal dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "two equal dimensions 5"
val a = 5
val b = 5
# When "broadcasting"
val result = broadcast_dim(a, b)
# Then "result should be 5"
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(5)
```

</details>

#### Broadcast 1 with larger dimension

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "dimensions 1 and 7"
val a = 1
val b = 7
# When "broadcasting"
val result = broadcast_dim(a, b)
# Then "result should be 7"
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(7)
```

</details>

#### Broadcast incompatible dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "dimensions 3 and 5"
val a = 3
val b = 5
# When "broadcasting"
val result = broadcast_dim(a, b)
# Then "it should return error"
expect(result.is_err()).to_equal(true)
```

</details>

#### Broadcast equal shapes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "two equal shapes [3, 4, 5]"
val a = [3, 4, 5]
val b = [3, 4, 5]
# When "broadcasting shapes"
val result = broadcast_shapes(a, b)
# Then "result should be [3, 4, 5]"
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal([3, 4, 5])
```

</details>

#### Broadcast with scalar (empty shape)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "shapes [3, 4] and []"
val a = [3, 4]
val b = []
# When "broadcasting shapes"
val result = broadcast_shapes(a, b)
# Then "result should be [3, 4]"
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal([3, 4])
```

</details>

#### Broadcast different lengths - compatible

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "shapes [3, 1, 5] and [4, 5]"
val a = [3, 1, 5]
val b = [4, 5]
# When "broadcasting shapes"
val result = broadcast_shapes(a, b)
# Then "result should be [3, 4, 5]"
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal([3, 4, 5])
```

</details>

#### Broadcast with 1s

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "shapes [1, 3, 1] and [2, 1, 4]"
val a = [1, 3, 1]
val b = [2, 1, 4]
# When "broadcasting shapes"
val result = broadcast_shapes(a, b)
# Then "result should be [2, 3, 4]"
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal([2, 3, 4])
```

</details>

#### Broadcast incompatible shapes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "shapes [3, 4] and [5]"
val a = [3, 4]
val b = [5]
# When "broadcasting shapes"
val result = broadcast_shapes(a, b)
# Then "it should return error"
expect(result.is_err()).to_equal(true)
```

</details>

#### Broadcast [256, 256, 3] and [3]

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "image shape and color channel"
val a = [256, 256, 3]
val b = [3]
# When "broadcasting shapes"
val result = broadcast_shapes(a, b)
# Then "result should be [256, 256, 3]"
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal([256, 256, 3])
```

</details>

#### Compute broadcast strides - same shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "shape [3, 4] broadcasting to [3, 4]"
val shape = [3, 4]
val target = [3, 4]
# When "computing broadcast strides"
val strides = compute_broadcast_strides(shape, target)
# Then "strides should be [4, 1] (normal)"
expect(strides).to_equal([4, 1])
```

</details>

#### Compute broadcast strides - with broadcasting

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "shape [1, 4] broadcasting to [3, 4]"
val shape = [1, 4]
val target = [3, 4]
# When "computing broadcast strides"
val strides = compute_broadcast_strides(shape, target)
# Then "first stride should be 0 (broadcast)"
expect(strides[0]).to_equal(0)
# And "second stride should be 1"
expect(strides[1]).to_equal(1)
```

</details>

#### Compute broadcast strides - scalar to vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "shape [] broadcasting to [5]"
val shape = []
val target = [5]
# When "computing broadcast strides"
val strides = compute_broadcast_strides(shape, target)
# Then "stride should be [0] (broadcast all)"
expect(strides).to_equal([0])
```

</details>

#### Can broadcast smaller to larger

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "shape [1, 5] and target [3, 5]"
val shape = [1, 5]
val target = [3, 5]
# When "checking if can broadcast"
val can = can_broadcast_to(shape, target)
# Then "it should return true"
expect(can).to_equal(true)
```

</details>

#### Cannot broadcast incompatible

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "shape [3, 4] and target [3, 5]"
val shape = [3, 4]
val target = [3, 5]
# When "checking if can broadcast"
val can = can_broadcast_to(shape, target)
# Then "it should return false"
expect(can).to_equal(false)
```

</details>

#### Can broadcast scalar to anything

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "empty shape and target [2, 3, 4]"
val shape = []
val target = [2, 3, 4]
# When "checking if can broadcast"
val can = can_broadcast_to(shape, target)
# Then "it should return true"
expect(can).to_equal(true)
```

</details>

#### Compute shape size

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a shape [2, 3, 4]"
val shape = [2, 3, 4]
# When "computing size"
val size = shape_size(shape)
# Then "size should be 24"
expect(size).to_equal(24)
```

</details>

#### Empty shape is scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an empty shape"
val shape = []
# When "checking if scalar"
val scalar = is_scalar(shape)
# Then "it should be scalar"
expect(scalar).to_equal(true)
```

</details>

#### 1D shape is vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a 1D shape [5]"
val shape = [5]
# When "checking if vector"
val vector_ok = is_vector(shape)
# Then "it should be vector"
expect(vector_ok).to_equal(true)
```

</details>

<details>
<summary>Advanced: 2D shape is matrix</summary>

#### 2D shape is matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a 2D shape [3, 4]"
val shape = [3, 4]
# When "checking if matrix"
val mat = is_matrix(shape)
# Then "it should be matrix"
expect(mat).to_equal(true)
```

</details>


</details>

#### Get number of dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a 3D shape [2, 3, 4]"
val shape = [2, 3, 4]
# When "getting ndim"
val nd = ndim(shape)
# Then "it should be 3"
expect(nd).to_equal(3)
```

</details>

#### Broadcast empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an empty list of shapes"
val shapes = []
# When "broadcasting many"
val result = broadcast_shapes_many(shapes)
# Then "result should be empty shape"
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal([])
```

</details>

#### Broadcast single shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a single shape [3, 4]"
val shapes = [[3, 4]]
# When "broadcasting many"
val result = broadcast_shapes_many(shapes)
# Then "result should be [3, 4]"
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal([3, 4])
```

</details>

#### Broadcast three compatible shapes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "shapes [3, 1, 5], [1, 4, 5], [3, 4, 1]"
val shapes = [[3, 1, 5], [1, 4, 5], [3, 4, 1]]
# When "broadcasting many"
val result = broadcast_shapes_many(shapes)
# Then "result should be [3, 4, 5]"
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal([3, 4, 5])
```

</details>

#### Broadcast incompatible shapes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "shapes [3, 4] and [5, 6]"
val shapes = [[3, 4], [5, 6]]
# When "broadcasting many"
val result = broadcast_shapes_many(shapes)
# Then "it should return error"
expect(result.is_err()).to_equal(true)
```

</details>

#### Check all compatible - true

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "compatible shapes"
val shapes = [[1, 5], [3, 1], [3, 5]]
# When "checking all compatible"
val compat = all_broadcast_compatible(shapes)
# Then "it should return true"
expect(compat).to_equal(true)
```

</details>

#### Check all compatible - false

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "incompatible shapes"
val shapes = [[3, 4], [5, 6]]
# When "checking all compatible"
val compat = all_broadcast_compatible(shapes)
# Then "it should return false"
expect(compat).to_equal(false)
```

</details>

#### Ravel 2D index

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "indices [1, 2] and strides [4, 1]"
val indices = [1, 2]
val strides = [4, 1]
# When "raveling to flat index"
val flat = ravel_index(indices, strides)
# Then "flat index should be 6 (1*4 + 2*1)"
expect(flat).to_equal(6)
```

</details>

#### Ravel 3D index

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "indices [1, 2, 3] and strides [12, 4, 1]"
val indices = [1, 2, 3]
val strides = [12, 4, 1]
# When "raveling to flat index"
val flat = ravel_index(indices, strides)
# Then "flat index should be 23 (1*12 + 2*4 + 3*1)"
expect(flat).to_equal(23)
```

</details>

#### Unravel flat index

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "flat index 23 and strides [12, 4, 1]"
val flat = 23
val strides = [12, 4, 1]
# When "unraveling to multi-dimensional"
val indices = unravel_index(flat, strides)
# Then "indices should be [1, 2, 3]"
expect(indices).to_equal([1, 2, 3])
```

</details>

#### Ravel and unravel round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "original indices [2, 1, 3] and strides [12, 4, 1]"
val original = [2, 1, 3]
val strides = [12, 4, 1]
# When "raveling then unraveling"
val flat = ravel_index(original, strides)
val recovered = unravel_index(flat, strides)
# Then "should recover original indices"
expect(recovered).to_equal(original)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/stdlib/math/tensor_broadcast_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 39 |
| Active scenarios | 39 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
