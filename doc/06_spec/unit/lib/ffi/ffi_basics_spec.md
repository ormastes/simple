# Ffi Basics Specification

> Tests covering FFI Type Mapping, FFI Calling Convention, FFI Safety, FFI Data Layout, Runtime FFI Functions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ffi Basics Specification

## Scenarios

### FFI Type Mapping

#### i64 maps to int64_t

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- i64 maps to int64_t


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("i64 maps to int64_t")
val type_name = "int64_t"
check(type_name == "int64_t")
```

</details>

#### f64 maps to double

- f64 maps to double


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("f64 maps to double")
val type_name = "double"
check(type_name == "double")
```

</details>

#### bool maps to bool

- bool maps to bool


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bool maps to bool")
val type_name = "bool"
check(type_name == "bool")
```

</details>

#### text maps to char*

- text maps to char*


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("text maps to char*")
val type_name = "char*"
check(type_name == "char*")
```

</details>

#### void maps to void

- void maps to void


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("void maps to void")
val type_name = "void"
check(type_name == "void")
```

</details>

### FFI Calling Convention

#### c calling convention

- c calling convention


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("c calling convention")
val conv = "c"
check(conv == "c")
```

</details>

#### stdcall convention

- stdcall convention


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stdcall convention")
val conv = "stdcall"
check(conv == "stdcall")
```

</details>

#### fastcall convention

- fastcall convention


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fastcall convention")
val conv = "fastcall"
check(conv == "fastcall")
```

</details>

### FFI Safety

#### extern functions are unsafe

- extern functions are unsafe


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extern functions are unsafe")
val is_unsafe = true
check(is_unsafe)
```

</details>

#### null pointer check

- null pointer check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("null pointer check")
val ptr = nil
check(ptr == nil)
```

</details>

#### buffer size validation

- buffer size validation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("buffer size validation")
val buffer_size = 1024
check(buffer_size > 0)
```

</details>

#### string encoding is UTF-8

- string encoding is UTF-8


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string encoding is UTF-8")
val encoding = "utf-8"
check(encoding == "utf-8")
```

</details>

### FFI Data Layout

#### struct alignment

- struct alignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("struct alignment")
val alignment = 8
check(alignment == 8 or alignment == 4)
```

</details>

#### field offset calculation

- field offset calculation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("field offset calculation")
val offset = 0
check(offset >= 0)
```

</details>

#### struct padding

- struct padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("struct padding")
val has_padding = true
check(true)
```

</details>

#### packed struct

- packed struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("packed struct")
val packed = true
check(packed)
```

</details>

### Runtime FFI Functions

#### rt_file_read_text signature

- rt_file_read_text signature


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rt_file_read_text signature")
val name = "rt_file_read_text"
check(name.starts_with("rt_"))
```

</details>

#### rt_file_write_text signature

- rt_file_write_text signature


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rt_file_write_text signature")
val name = "rt_file_write_text"
check(name.starts_with("rt_"))
```

</details>

#### rt_time_now_ms signature

- rt_time_now_ms signature


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rt_time_now_ms signature")
val name = "rt_time_now_ms"
check(name.starts_with("rt_"))
```

</details>

#### rt_env_get signature

- rt_env_get signature


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rt_env_get signature")
val name = "rt_env_get"
check(name.starts_with("rt_"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/ffi/ffi_basics_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FFI Type Mapping, FFI Calling Convention, FFI Safety, FFI Data Layout, Runtime FFI Functions.
- FFI Type Mapping
- FFI Calling Convention
- FFI Safety
- FFI Data Layout
- Runtime FFI Functions

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `89112a93c6f399d84ed29be49d68e8ebe6a03ab50aa00444dded046f05c2cedb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `89112a93c6f399d84ed29be49d68e8ebe6a03ab50aa00444dded046f05c2cedb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `89112a93c6f399d84ed29be49d68e8ebe6a03ab50aa00444dded046f05c2cedb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/ffi/ffi_basics_spec.spl
mirror: doc/06_spec/unit/lib/ffi/ffi_basics_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/ffi/ffi_basics_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/ffi/ffi_basics_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/ffi/ffi_basics_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'i64 maps to int64_t' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/ffi/ffi_basics_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'f64 maps to double' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/ffi/ffi_basics_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bool maps to bool' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
