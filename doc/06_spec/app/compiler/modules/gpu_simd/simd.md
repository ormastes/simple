## Part 1: SIMD Vector Types

### Vector Type Syntax

SIMD vectors are fixed-size, homogeneous arrays optimized for parallel arithmetic:

```simple
# Vector type syntax: vec[N, T] where N is lane count, T is element type
let v1: vec[4, f32] = vec[1.0, 2.0, 3.0, 4.0]
let v2: vec[8, i32] = vec[1, 2, 3, 4, 5, 6, 7, 8]

# Type aliases for common sizes
type f32x4 = vec[4, f32]
type f32x8 = vec[8, f32]
type i32x4 = vec[4, i32]
type i32x8 = vec[8, i32]
```

### Supported Lane Counts

| Type | 2-lane | 4-lane | 8-lane | 16-lane |
|------|--------|--------|--------|---------|
| f64 | vec[2, f64] | vec[4, f64] | vec[8, f64] | - |
| f32 | vec[2, f32] | vec[4, f32] | vec[8, f32] | vec[16, f32] |
| i64 | vec[2, i64] | vec[4, i64] | vec[8, i64] | - |
| i32 | vec[2, i32] | vec[4, i32] | vec[8, i32] | vec[16, i32] |
| i16 | vec[2, i16] | vec[4, i16] | vec[8, i16] | vec[16, i16] |
| i8 | vec[2, i8] | vec[4, i8] | vec[8, i8] | vec[16, i8] |
| bool | vec[2, bool] | vec[4, bool] | vec[8, bool] | vec[16, bool] |

### Vector Operations

#### Arithmetic (Lane-wise)

```simple
let a: f32x4 = vec[1.0, 2.0, 3.0, 4.0]
let b: f32x4 = vec[5.0, 6.0, 7.0, 8.0]

let sum = a + b       # vec[6.0, 8.0, 10.0, 12.0]
let diff = a - b      # vec[-4.0, -4.0, -4.0, -4.0]
let prod = a * b      # vec[5.0, 12.0, 21.0, 32.0]
let quot = a / b      # vec[0.2, 0.333..., 0.428..., 0.5]
```

#### Comparison (Returns bool vector)

```simple
let mask = a < b      # vec[true, true, true, true]
let eq = a == b       # vec[false, false, false, false]
```

#### Reductions

```simple
let total = a.sum()           # 10.0 (horizontal sum)
let product = a.product()     # 24.0 (horizontal product)
let maximum = a.max()         # 4.0
let minimum = a.min()         # 1.0
let all_positive = (a > 0.0).all()  # true
let any_negative = (a < 0.0).any()  # false
```

#### Shuffles and Swizzles

```simple
# Named swizzle (for vec[2-4])
let v: f32x4 = vec[1.0, 2.0, 3.0, 4.0]
let swapped = v.yxzw          # vec[2.0, 1.0, 3.0, 4.0]
let broadcast = v.xxxx        # vec[1.0, 1.0, 1.0, 1.0]

# Index shuffle (for any size)
let shuffled = v.shuffle([3, 2, 1, 0])  # vec[4.0, 3.0, 2.0, 1.0]

# Cross-vector shuffle
let merged = a.blend(b, [0, 1, 4, 5])   # Takes indices, 0-3 from a, 4-7 from b
```

#### Lane Access

```simple
let v: f32x4 = vec[1.0, 2.0, 3.0, 4.0]
let first = v[0]              # 1.0 (extract)
let modified = v.with(2, 9.0) # vec[1.0, 2.0, 9.0, 4.0] (immutable update)
```

#### Load/Store

```simple
# Load from array (aligned)
let arr: [f32; 8] = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]
let v1 = f32x4.load(arr, 0)   # Load from index 0
let v2 = f32x4.load(arr, 4)   # Load from index 4

# Store to array
v1.store(arr, 0)

# Gather (indexed load)
let indices: i32x4 = vec[0, 2, 4, 6]
let gathered = f32x4.gather(arr, indices)  # vec[1.0, 3.0, 5.0, 7.0]

# Scatter (indexed store)
v1.scatter(arr, indices)
```

#### Math Functions

```simple
let v: f32x4 = vec[1.0, 4.0, 9.0, 16.0]

let sqrts = v.sqrt()          # vec[1.0, 2.0, 3.0, 4.0]
let recip = v.recip()         # vec[1.0, 0.25, 0.111..., 0.0625]
let abs_v = (-v).abs()        # vec[1.0, 4.0, 9.0, 16.0]
let floor_v = v.floor()
let ceil_v = v.ceil()
let round_v = v.round()

# Fused multiply-add (a * b + c)
let fma = a.fma(b, c)         # More accurate than a * b + c
```

#### Masked Operations

```simple
let mask: vec[4, bool] = vec[true, false, true, false]
let a: f32x4 = vec[1.0, 2.0, 3.0, 4.0]
let b: f32x4 = vec[5.0, 6.0, 7.0, 8.0]

# Select: mask ? a : b
let selected = mask.select(a, b)  # vec[1.0, 6.0, 3.0, 8.0]

# Masked load (load only where mask is true)
let loaded = f32x4.load_masked(arr, 0, mask, 0.0)  # 0.0 for masked lanes

# Masked store (store only where mask is true)
a.store_masked(arr, 0, mask)
```

### SIMD Best Practices

```simple
# Prefer wider vectors when hardware supports it
const SIMD_WIDTH = simd.preferred_width[f32]()  # 4, 8, or 16 depending on CPU

# Process arrays in chunks
fn process_array(data: &mut [f32]):
    let chunks = data.len() / SIMD_WIDTH
    for i in 0..chunks:
        let v = f32x4.load(data, i * SIMD_WIDTH)
        let result = v * 2.0 + 1.0
        result.store(data, i * SIMD_WIDTH)

    # Handle remainder with scalar code
    for i in (chunks * SIMD_WIDTH)..data.len():
        data[i] = data[i] * 2.0 + 1.0
```

---


## Part 4: Indexer Trait and Neighbor Accessors

### 4.1 User-Defined Indexers

A class may declare an indexer signature:

```simple
class Matrix indexer(i: i32, j: i32) -> f32:
    data: f32[]
    width: i32

    fn get(self, i: i32, j: i32) -> f32:
        return self.data[i * self.width + j]

    fn set(self, i: i32, j: i32, v: f32):
        self.data[i * self.width + j] = v
```

Compiler desugaring:
- `m[i, j]` in rvalue context -> `m.get(i, j)`
- `m[i, j] = v` -> `m.set(i, j, v)`

### 4.2 Indexer Forwarding (`@indexer` field)

A class may mark exactly one field as the default forwarded indexer:

```simple
class AudioBuffer:
    @indexer samples: f32[]
```

Then `buf[i]` forwards to `buf.samples[i]`.

### 4.3 Neighbor Accessors

For indexables with 1D integer indexing, the following postfix properties are available in `@simd` contexts:

- `.left_neighbor` -> element at `index - 1`
- `.right_neighbor` -> element at `index + 1`

Context rule: the "current index" is the kernel's `this.index()`.

Bounds behavior: Neighbor access triggers bounds events and is governed by `@bounds` / `bounds:`.

```simple
@simd
fn blur_1d(x: f32[], out: f32[]):
    let i = this.index()
    let left  = x.left_neighbor
    let mid   = x[i]
    let right = x.right_neighbor
    out[i] = (left + mid + right) / 3.0

bounds:
    _.x.under || _.x.over:
        return
    _.out.under || _.out.over:
        return
```

---


## Part 5: Data Parallel Operations

Higher-level abstractions built on GPU/SIMD:

### Parallel Iterators

```simple
use parallel

# Parallel map (auto-selects SIMD or GPU)
let result = data.par_map(\x: x * 2.0 + 1.0)

# Parallel reduce
let sum = data.par_reduce(0.0, \a, b: a + b)

# Parallel filter
let positive = data.par_filter(\x: x > 0.0)

# Parallel for_each
data.par_for_each \x:
    print x
```

### Parallel Configuration

```simple
use parallel

# Configure parallelism
parallel.set_config(
    simd_enabled: true,
    gpu_enabled: true,
    gpu_threshold: 10000,    # Min elements before using GPU
    thread_count: 8          # For CPU parallelism
)

# Force specific backend
let result = data.par_map(backend: :gpu, \x: x * 2.0)
let result = data.par_map(backend: :simd, \x: x * 2.0)
let result = data.par_map(backend: :cpu, \x: x * 2.0)
```

### Tensor Operations (Preview)

```simple
use tensor

# Create tensors
let a = Tensor.new[[f32; 3, 3]]([
    [1.0, 2.0, 3.0],
    [4.0, 5.0, 6.0],
    [7.0, 8.0, 9.0]
])

let b = Tensor.zeros[[f32; 3, 3]]()
let c = Tensor.ones[[f32; 3, 3]]()

# Operations (auto-parallelized)
let d = a @ b                 # Matrix multiply
let e = a + b                 # Element-wise add
let f = a.transpose()         # Transpose
let g = a.sum(axis: 0)        # Reduce along axis
```

---

