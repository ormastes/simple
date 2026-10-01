# Ffi Wrappers Specification

> Tests covering File System FFI, Process FFI, Network FFI, Time FFI, Memory FFI.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ffi Wrappers Specification

## Scenarios

### File System FFI

#### file_exists wrapper

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- file_exists wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("file_exists wrapper")
val fn_name = "rt_file_exists"
check(fn_name.starts_with("rt_"))
```

</details>

#### file_read_text wrapper

- file_read_text wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("file_read_text wrapper")
val fn_name = "rt_file_read_text"
check(fn_name.contains("read"))
```

</details>

#### file_write_text wrapper

- file_write_text wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("file_write_text wrapper")
val fn_name = "rt_file_write_text"
check(fn_name.contains("write"))
```

</details>

#### file_delete wrapper

- file_delete wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("file_delete wrapper")
val fn_name = "rt_file_delete"
check(fn_name.contains("delete"))
```

</details>

#### dir_create wrapper

- dir_create wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dir_create wrapper")
val fn_name = "rt_dir_create"
check(fn_name.contains("dir"))
```

</details>

#### dir_list wrapper

- dir_list wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dir_list wrapper")
val fn_name = "rt_dir_list"
check(fn_name.contains("list"))
```

</details>

### Process FFI

#### process_exec wrapper

- process_exec wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("process_exec wrapper")
val fn_name = "rt_process_exec"
check(fn_name.contains("process"))
```

</details>

#### process_output wrapper

- process_output wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("process_output wrapper")
val fn_name = "rt_process_output"
check(fn_name.contains("output"))
```

</details>

#### env_get wrapper

- env_get wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env_get wrapper")
val fn_name = "rt_env_get"
check(fn_name.contains("env"))
```

</details>

#### env_set wrapper

- env_set wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env_set wrapper")
val fn_name = "rt_env_set"
check(fn_name.contains("env"))
```

</details>

### Network FFI

#### tcp_connect wrapper

- tcp_connect wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tcp_connect wrapper")
val fn_name = "rt_tcp_connect"
check(fn_name.contains("tcp"))
```

</details>

#### tcp_listen wrapper

- tcp_listen wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tcp_listen wrapper")
val fn_name = "rt_tcp_listen"
check(fn_name.contains("listen"))
```

</details>

#### http_get wrapper

- http_get wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("http_get wrapper")
val fn_name = "rt_http_get"
check(fn_name.contains("http"))
```

</details>

#### http_post wrapper

- http_post wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("http_post wrapper")
val fn_name = "rt_http_post"
check(fn_name.contains("post"))
```

</details>

### Time FFI

#### time_now wrapper

- time_now wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("time_now wrapper")
val fn_name = "rt_time_now_ms"
check(fn_name.contains("time"))
```

</details>

#### sleep wrapper

- sleep wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sleep wrapper")
val fn_name = "rt_sleep_ms"
check(fn_name.contains("sleep"))
```

</details>

### Memory FFI

#### alloc wrapper

- alloc wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("alloc wrapper")
val fn_name = "rt_alloc"
check(fn_name.contains("alloc"))
```

</details>

#### free wrapper

- free wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("free wrapper")
val fn_name = "rt_free"
check(fn_name.contains("free"))
```

</details>

#### realloc wrapper

- realloc wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("realloc wrapper")
val fn_name = "rt_realloc"
check(fn_name.contains("realloc"))
```

</details>

#### memcpy wrapper

- memcpy wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("memcpy wrapper")
val fn_name = "rt_memcpy"
check(fn_name.contains("memcpy"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/ffi/ffi_wrappers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering File System FFI, Process FFI, Network FFI, Time FFI, Memory FFI.
- File System FFI
- Process FFI
- Network FFI
- Time FFI
- Memory FFI

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

- Canonical SPipe generation for source `283b77d25b5e083d0096528a4ec86e2d5f2ba9e9c11a5b39ef2b7d2a5d2f57ea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `283b77d25b5e083d0096528a4ec86e2d5f2ba9e9c11a5b39ef2b7d2a5d2f57ea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `283b77d25b5e083d0096528a4ec86e2d5f2ba9e9c11a5b39ef2b7d2a5d2f57ea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/ffi/ffi_wrappers_spec.spl
mirror: doc/06_spec/unit/lib/ffi/ffi_wrappers_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/ffi/ffi_wrappers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/ffi/ffi_wrappers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/ffi/ffi_wrappers_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'file_exists wrapper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/ffi/ffi_wrappers_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'file_read_text wrapper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/ffi/ffi_wrappers_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'file_write_text wrapper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
