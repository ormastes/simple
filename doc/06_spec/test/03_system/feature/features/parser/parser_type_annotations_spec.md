# Parser Type Annotations Specification

> let v: vec[4, f32] = simd_vec

<!-- sdn-diagram:id=parser_type_annotations_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_type_annotations_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_type_annotations_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_type_annotations_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Type Annotations Specification

let v: vec[4, f32] = simd_vec

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-TYPE-001 to #PARSER-TYPE-012 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/features/parser/parser_type_annotations_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Type Syntax

```simple
# SIMD vectors
let v: vec[4, f32] = simd_vec

# Unit types
unit UserId: i64 as uid
unit IpAddr: str | u32 as ip

# Typed strings
let addr = "127.0.0.1"_ip
let path = 'C:/data.txt'_file

# Array types
let arr: [i32] = []       # Dynamic
let fixed: [i32; 10] = [] # Fixed size
```

## Scenarios

### SIMD Type Parsing

#### parses vec[4, f32] type

1. fn accepts vec4


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn accepts_vec4(v: vec[4, f32]) -> bool:
    true
expect true
```

</details>

#### parses vec[8, i32] type

1. fn accepts vec8


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn accepts_vec8(v: vec[8, i32]) -> bool:
    true
expect true
```

</details>

#### parses vec[2, f64] type

1. fn accepts vec2


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn accepts_vec2(v: vec[2, f64]) -> bool:
    true
expect true
```

</details>

#### parses SIMD function parameters

1. fn add vectors


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add_vectors(a: vec[4, f32], b: vec[4, f32]) -> vec[4, f32]:
    a  # placeholder
expect true
```

</details>

#### parses SIMD return type

1. fn get vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_vector() -> vec[4, f32]:
    nil
expect true
```

</details>

### Unit Type Declarations

#### single base unit

#### parses unit with single base type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit UserId: i64 as uid
val id: UserId = 42_uid
expect true
```

</details>

#### parses unit with suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit Temperature: f64 as deg
val temp: Temperature = 98.6_deg
expect true
```

</details>

#### multi-base unit

#### parses unit with two base types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit IpAddr: str | u32 as ip
expect true
```

</details>

#### parses unit with multiple base types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit MacAddr: str | u64 as mac
expect true
```

</details>

### Typed String Literals

#### parses string with _ip suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit IpAddr: str as ip
val addr = "127.0.0.1"_ip
expect true
```

</details>

#### parses raw string with _file suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit FilePath: str as file
val path = 'C:/Users/data.txt'_file
expect true
```

</details>

#### parses string with _http suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit HttpUrl: str as http
val url = "https://example.com"_http
expect true
```

</details>

#### parses string with custom suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit Email: str as email
val addr = "user@example.com"_email
expect true
```

</details>

### Array Type Syntax

#### dynamic arrays

#### parses [i32] type

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i32] = [1, 2, 3]
expect arr.len() == 3
```

</details>

#### parses [str] type

1. expect names len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names: [str] = ["a", "b", "c"]
expect names.len() == 3
```

</details>

#### parses nested array type

1. expect matrix len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix: [[i32]] = [[1, 2], [3, 4]]
expect matrix.len() == 2
```

</details>

#### fixed-size arrays

#### parses [i32; 10] type

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i32; 10] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
expect arr.len() == 10
```

</details>

#### parses [f64; 3] type

1. expect values len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values: [f64; 3] = [1.0, 2.0, 3.0]
expect values.len() == 3
```

</details>

### Generic Type Annotations

#### parses Option<T> type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = Some(42)
expect opt.?
```

</details>

#### parses Result<T, E> type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res: Result<i64, str> = Ok(42)
expect res.ok.?
```

</details>

#### parses nested generic type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<Option<i64>> = Some(Some(42))
expect opt.?
```

</details>

#### parses generic with multiple params

1. expect map len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map: Dict<str, i64> = {"a": 1}
expect map.len() == 1
```

</details>

### Function Type Annotations

#### parses fn type annotation

1. expect f


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f: fn(i64) -> i64 = \x: x * 2
expect f(21) == 42
```

</details>

#### parses fn with multiple params

1. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val add: fn(i64, i64) -> i64 = \a, b: a + b
expect add(20, 22) == 42
```

</details>

#### parses fn returning unit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val printer: fn(str) -> () = \s: print(s)
expect true
```

</details>

### Tuple Type Annotations

#### parses (i64, str) type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pair: (i64, str) = (42, "hello")
expect pair.0 == 42
```

</details>

#### parses triple tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple: (i64, str, bool) = (1, "a", true)
expect triple.2 == true
```

</details>

#### parses nested tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nested: ((i64, i64), str) = ((1, 2), "point")
expect nested.0.0 == 1
```

</details>

### Reference Type Annotations

#### parses mutable reference

1. fn modify
2. expect modify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verifies that `mut` parameter annotation parses correctly.
# Parameters are passed by value in the interpreter, so mutation
# is local to the function — the return value validates parsing succeeded.
fn modify(x: mut i64) -> i64:
    x + 1
val n = 41
expect modify(n) == 42
```

</details>

#### parses immutable reference

1. fn read only
2. expect read only


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn read_only(x: i64) -> i64:
    x * 2
val n = 21
expect read_only(n) == 42
```

</details>

### Complex Type Combinations

#### parses Option<[i64]>

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<[i64]> = Some([1, 2, 3])
expect opt.?
```

</details>

#### parses Result<(i64, str), str>

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res: Result<(i64, str), str> = Ok((42, "answer"))
expect res.ok.?
```

</details>

#### parses fn returning Option

1. expect f


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f: fn(i64) -> Option<i64> = \x: if x > 0: Some(x) else: nil
expect f(42).?
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
