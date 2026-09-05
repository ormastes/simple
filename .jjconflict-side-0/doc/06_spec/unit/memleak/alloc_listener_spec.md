# Alloc Listener Specification

> Tests covering WI-2: Allocation listener types in header, WI-2: Listener callback typedef, WI-2: Listener implementation, WI-2: Simple FFI wrappers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Alloc Listener Specification

## Scenarios

### WI-2: Allocation listener types in header

#### SplAllocEventKind enum defined

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- SplAllocEventKind enum defined
   - Expected: content contains `SplAllocEventKind`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SplAllocEventKind enum defined")
val content = rt_file_read_text("src/runtime/runtime_memtrack.h") ?? ""
expect(content.contains("SplAllocEventKind")).to_equal(true)
```

</details>

#### SPL_ALLOC_MALLOC defined

- SPL_ALLOC_MALLOC defined
   - Expected: content contains `SPL_ALLOC_MALLOC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SPL_ALLOC_MALLOC defined")
val content = rt_file_read_text("src/runtime/runtime_memtrack.h") ?? ""
expect(content.contains("SPL_ALLOC_MALLOC")).to_equal(true)
```

</details>

#### SPL_ALLOC_FREE defined

- SPL_ALLOC_FREE defined
   - Expected: content contains `SPL_ALLOC_FREE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SPL_ALLOC_FREE defined")
val content = rt_file_read_text("src/runtime/runtime_memtrack.h") ?? ""
expect(content.contains("SPL_ALLOC_FREE")).to_equal(true)
```

</details>

#### SplAllocEvent struct defined

- SplAllocEvent struct defined
   - Expected: content contains `SplAllocEvent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SplAllocEvent struct defined")
val content = rt_file_read_text("src/runtime/runtime_memtrack.h") ?? ""
expect(content.contains("SplAllocEvent")).to_equal(true)
```

</details>

#### SplAllocEvent has kind field

- SplAllocEvent has kind field
   - Expected: content contains `SplAllocEventKind kind`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SplAllocEvent has kind field")
val content = rt_file_read_text("src/runtime/runtime_memtrack.h") ?? ""
expect(content.contains("SplAllocEventKind kind")).to_equal(true)
```

</details>

#### SplAllocEvent has ptr field

- SplAllocEvent has ptr field
   - Expected: content contains `void*       ptr`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SplAllocEvent has ptr field")
val content = rt_file_read_text("src/runtime/runtime_memtrack.h") ?? ""
expect(content.contains("void*       ptr")).to_equal(true)
```

</details>

#### SplAllocEvent has alloc_id field

- SplAllocEvent has alloc_id field
   - Expected: content contains `int64_t     alloc_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SplAllocEvent has alloc_id field")
val content = rt_file_read_text("src/runtime/runtime_memtrack.h") ?? ""
expect(content.contains("int64_t     alloc_id")).to_equal(true)
```

</details>

### WI-2: Listener callback typedef

#### spl_alloc_listener_fn typedef defined

- spl_alloc_listener_fn typedef defined
   - Expected: content contains `spl_alloc_listener_fn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spl_alloc_listener_fn typedef defined")
val content = rt_file_read_text("src/runtime/runtime_memtrack.h") ?? ""
expect(content.contains("spl_alloc_listener_fn")).to_equal(true)
```

</details>

#### set_listener function declared

- set_listener function declared
   - Expected: content contains `spl_memtrack_set_listener`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_listener function declared")
val content = rt_file_read_text("src/runtime/runtime_memtrack.h") ?? ""
expect(content.contains("spl_memtrack_set_listener")).to_equal(true)
```

</details>

#### clear_listener function declared

- clear_listener function declared
   - Expected: content contains `spl_memtrack_clear_listener`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear_listener function declared")
val content = rt_file_read_text("src/runtime/runtime_memtrack.h") ?? ""
expect(content.contains("spl_memtrack_clear_listener")).to_equal(true)
```

</details>

### WI-2: Listener implementation

#### g_listener_fn static variable exists

- g_listener_fn static variable exists
   - Expected: content contains `g_listener_fn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("g_listener_fn static variable exists")
val content = rt_file_read_text("src/runtime/runtime_memtrack.c") ?? ""
expect(content.contains("g_listener_fn")).to_equal(true)
```

</details>

#### g_listener_data static variable exists

- g_listener_data static variable exists
   - Expected: content contains `g_listener_data`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("g_listener_data static variable exists")
val content = rt_file_read_text("src/runtime/runtime_memtrack.c") ?? ""
expect(content.contains("g_listener_data")).to_equal(true)
```

</details>

#### record() dispatches to listener

- record() dispatches to listener
   - Expected: content contains `g_listener_fn(&ev, g_listener_data)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("record() dispatches to listener")
val content = rt_file_read_text("src/runtime/runtime_memtrack.c") ?? ""
# spl_memtrack_record should call g_listener_fn when set
expect(content.contains("g_listener_fn(&ev, g_listener_data)")).to_equal(true)
```

</details>

#### unrecord() dispatches to listener before removing

- unrecord() dispatches to listener before removing
   - Expected: content contains `ev.kind     = SPL_ALLOC_FREE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unrecord() dispatches to listener before removing")
val content = rt_file_read_text("src/runtime/runtime_memtrack.c") ?? ""
# spl_memtrack_unrecord should notify listener with SPL_ALLOC_FREE
expect(content.contains("ev.kind     = SPL_ALLOC_FREE")).to_equal(true)
```

</details>

#### set_listener implementation exists

- set_listener implementation exists
   - Expected: content contains `void spl_memtrack_set_listener`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_listener implementation exists")
val content = rt_file_read_text("src/runtime/runtime_memtrack.c") ?? ""
expect(content.contains("void spl_memtrack_set_listener")).to_equal(true)
```

</details>

#### clear_listener sets to NULL

- clear_listener sets to NULL
   - Expected: content contains `void spl_memtrack_clear_listener`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear_listener sets to NULL")
val content = rt_file_read_text("src/runtime/runtime_memtrack.c") ?? ""
expect(content.contains("void spl_memtrack_clear_listener")).to_equal(true)
```

</details>

### WI-2: Simple FFI wrappers

#### mem_tracker/mod.spl exports listener functions

- mem_tracker/mod.spl exports listener functions
   - Expected: content contains `mem_set_listener`
   - Expected: content contains `mem_clear_listener`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mem_tracker/mod.spl exports listener functions")
val content = rt_file_read_text("src/lib/nogc_sync_mut/mem_tracker/mod.spl") ?? ""
expect(content.contains("mem_set_listener")).to_equal(true)
expect(content.contains("mem_clear_listener")).to_equal(true)
```

</details>

#### extern declaration for set_listener

- extern declaration for set_listener
   - Expected: content contains `extern fn spl_memtrack_set_listener`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extern declaration for set_listener")
val content = rt_file_read_text("src/lib/nogc_sync_mut/mem_tracker/mod.spl") ?? ""
expect(content.contains("extern fn spl_memtrack_set_listener")).to_equal(true)
```

</details>

#### extern declaration for clear_listener

- extern declaration for clear_listener
   - Expected: content contains `extern fn spl_memtrack_clear_listener`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extern declaration for clear_listener")
val content = rt_file_read_text("src/lib/nogc_sync_mut/mem_tracker/mod.spl") ?? ""
expect(content.contains("extern fn spl_memtrack_clear_listener")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Memory Safety |
| Status | Active |
| Source | `test/unit/memleak/alloc_listener_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WI-2: Allocation listener types in header, WI-2: Listener callback typedef, WI-2: Listener implementation, WI-2: Simple FFI wrappers.
- WI-2: Allocation listener types in header
- WI-2: Listener callback typedef
- WI-2: Listener implementation
- WI-2: Simple FFI wrappers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `53d76f15d8dfc6864600afa2373aabcd5551af5f4290a545d56c56659d4471a7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `53d76f15d8dfc6864600afa2373aabcd5551af5f4290a545d56c56659d4471a7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `53d76f15d8dfc6864600afa2373aabcd5551af5f4290a545d56c56659d4471a7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/memleak/alloc_listener_spec.spl
mirror: doc/06_spec/unit/memleak/alloc_listener_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/memleak/alloc_listener_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/memleak/alloc_listener_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/memleak/alloc_listener_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SplAllocEventKind enum defined' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/memleak/alloc_listener_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SPL_ALLOC_MALLOC defined' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/memleak/alloc_listener_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SPL_ALLOC_FREE defined' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
