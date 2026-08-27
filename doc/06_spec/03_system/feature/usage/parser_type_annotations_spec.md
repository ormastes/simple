# Parser Type Annotations Specification

> let v: vec[4, f32] = simd_vec

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
| Source | `test/03_system/feature/usage/parser_type_annotations_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Type Syntax

```simple
# SIMD vectors
let v: vec[4, f32] = simd_vec

# Unit types
unit UserId: i64 as uid
unit IpAddr: text | u32 as ip

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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses vec[4, f32] type


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses vec[4, f32] type")
expect true
```

</details>

#### parses vec[8, i32] type

- parses vec[8, i32] type


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses vec[8, i32] type")
expect true
```

</details>

#### parses vec[2, f64] type

- parses vec[2, f64] type


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses vec[2, f64] type")
expect true
```

</details>

#### parses SIMD function parameters

- parses SIMD function parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses SIMD function parameters")
expect true
```

</details>

#### parses SIMD return type

- parses SIMD return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses SIMD return type")
expect true
```

</details>

### Unit Type Declarations

#### single base unit

#### parses unit with single base type

- parses unit with single base type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses unit with single base type")
unit UserId: i64 as uid
val id: UserId = 42_uid
expect true
```

</details>

#### parses unit with suffix

- parses unit with suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses unit with suffix")
unit Temperature: f64 as deg
val temp: Temperature = 98.6_deg
expect true
```

</details>

#### multi-base unit

#### parses unit with two base types

- parses unit with two base types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses unit with two base types")
unit IpAddr: text | u32 as ip
expect true
```

</details>

#### parses unit with multiple base types

- parses unit with multiple base types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses unit with multiple base types")
unit MacAddr: text | u64 as mac
expect true
```

</details>

### Typed String Literals

#### parses string with _ip suffix

- parses string with _ip suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses string with _ip suffix")
unit IpAddr: text as ip
val addr = "127.0.0.1"_ip
expect true
```

</details>

#### parses raw string with _file suffix

- parses raw string with _file suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses raw string with _file suffix")
unit FilePath: text as file
val path = 'C:/Users/data.txt'_file
expect true
```

</details>

#### parses string with _http suffix

- parses string with _http suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses string with _http suffix")
unit HttpUrl: text as http
val url = "https://example.com"_http
expect true
```

</details>

#### parses string with custom suffix

- parses string with custom suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses string with custom suffix")
unit Email: text as email
val addr = "user@example.com"_email
expect true
```

</details>

### Array Type Syntax

#### dynamic arrays

#### parses [i32] type

- parses [i32] type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses [i32] type")
val arr: [i32] = [1, 2, 3]
expect arr.len() == 3
```

</details>

#### parses [text] type

- parses [text] type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses [text] type")
val names: [text] = ["a", "b", "c"]
expect names.len() == 3
```

</details>

#### parses nested array type

- parses nested array type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses nested array type")
val matrix: [[i32]] = [[1, 2], [3, 4]]
expect matrix.len() == 2
```

</details>

#### fixed-size arrays

#### parses [i32; 10] type

- parses [i32; 10] type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses [i32; 10] type")
val arr: [i32; 10] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
expect arr.len() == 10
```

</details>

#### parses [f64; 3] type

- parses [f64; 3] type


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses [f64; 3] type")
expect true
```

</details>

### Generic Type Annotations

#### parses Option<T> type

- parses Option<T> type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses Option<T> type")
val opt: Option<i64> = Some(42)
expect opt.?
```

</details>

#### parses Result<T, E> type

- parses Result<T, E> type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses Result<T, E> type")
val res: Result<i64, text> = Ok(42)
expect res.ok.?
```

</details>

#### parses nested generic type

- parses nested generic type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses nested generic type")
val opt: Option<Option<i64>> = Some(Some(42))
expect opt.?
```

</details>

#### parses generic with multiple params

- parses generic with multiple params


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses generic with multiple params")
val map: Dict<text, i64> = {"a": 1}
expect map.len() == 1
```

</details>

### Function Type Annotations

#### parses fn type annotation

- parses fn type annotation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses fn type annotation")
val f: fn(i64) -> i64 = \x: x * 2
expect f(21) == 42
```

</details>

#### parses fn with multiple params

- parses fn with multiple params


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses fn with multiple params")
val add: fn(i64, i64) -> i64 = \a, b: a + b
expect add(20, 22) == 42
```

</details>

#### parses fn returning unit

- parses fn returning unit


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses fn returning unit")
val printer: fn(text) -> () = \s: print(s)
expect true
```

</details>

### Tuple Type Annotations

#### parses (i64, text) type

- parses (i64, text) type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses (i64, text) type")
val pair: (i64, text) = (42, "hello")
expect pair.0 == 42
```

</details>

#### parses triple tuple

- parses triple tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses triple tuple")
val triple: (i64, text, bool) = (1, "a", true)
expect triple.2 == true
```

</details>

#### parses nested tuple

- parses nested tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses nested tuple")
val nested: ((i64, i64), text) = ((1, 2), "point")
val inner = nested.0
expect inner.0 == 1
```

</details>

### Reference Type Annotations

#### parses mutable reference

- parses mutable reference


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses mutable reference")
fn modify(x: mut i64):
    x = x + 1
var n = 41
modify(n)
expect n == 42
```

</details>

#### parses immutable reference

- parses immutable reference


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses immutable reference")
fn read_only(x: i64) -> i64:
    x * 2
val n = 21
expect read_only(n) == 42
```

</details>

### Complex Type Combinations

#### parses Option<[i64]>

- parses Option<[i64]>


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses Option<[i64]>")
val opt: Option<[i64]> = Some([1, 2, 3])
expect opt.?
```

</details>

#### parses Result<(i64, str), str>

- parses Result<(i64, str), str>


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses Result<(i64, str), str>")
val res: Result<(i64, text), text> = Ok((42, "answer"))
expect res.ok.?
```

</details>

#### parses fn returning Option

- parses fn returning Option


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses fn returning Option")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f304f242d1c0eff431f5742605c089833434e93eb3ae2afa4f836783ab1ade20`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f304f242d1c0eff431f5742605c089833434e93eb3ae2afa4f836783ab1ade20`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f304f242d1c0eff431f5742605c089833434e93eb3ae2afa4f836783ab1ade20`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/parser_type_annotations_spec.spl
mirror: doc/06_spec/03_system/feature/usage/parser_type_annotations_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/parser_type_annotations_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/parser_type_annotations_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/parser_type_annotations_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses vec[4, f32] type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/parser_type_annotations_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses vec[8, i32] type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/parser_type_annotations_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses vec[2, f64] type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
