# Fork Alloc Tracking Specification

> Tests covering WI-1: runtime_fork.c includes memtrack header, WI-1: Fork buffer allocations tracked, WI-1: Fork result cleanup tracked, WI-1: No raw malloc/free in fork functions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fork Alloc Tracking Specification

## Scenarios

### WI-1: runtime_fork.c includes memtrack header

#### includes runtime_memtrack.h

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- includes runtime_memtrack.h
   - Expected: content contains `#include "runtime_memtrack.h"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes runtime_memtrack.h")
val content = rt_file_read_text("src/runtime/runtime_fork.c") ?? ""
expect(content.contains("#include \"runtime_memtrack.h\"")).to_equal(true)
```

</details>

### WI-1: Fork buffer allocations tracked

#### stdout buffer uses SPL_MALLOC with fork_buf tag

- stdout buffer uses SPL_MALLOC with fork_buf tag
   - Expected: content contains `SPL_MALLOC(FORK_CAPTURE_LIMIT + FORK_CAPTURE_MARKER_MAX + 1U, "fork_buf")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stdout buffer uses SPL_MALLOC with fork_buf tag")
val content = rt_file_read_text("src/runtime/runtime_fork.c") ?? ""
expect(content.contains("SPL_MALLOC(FORK_CAPTURE_LIMIT + FORK_CAPTURE_MARKER_MAX + 1U, \"fork_buf\")")).to_equal(true)
```

</details>

#### stderr buffer uses SPL_MALLOC with fork_buf tag

- stderr buffer uses SPL_MALLOC with fork_buf tag
   - Expected: content contains `SPL_MALLOC(FORK_CAPTURE_LIMIT + FORK_CAPTURE_MARKER_MAX + 1U, "fork_buf")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stderr buffer uses SPL_MALLOC with fork_buf tag")
val content = rt_file_read_text("src/runtime/runtime_fork.c") ?? ""
expect(content.contains("SPL_MALLOC(FORK_CAPTURE_LIMIT + FORK_CAPTURE_MARKER_MAX + 1U, \"fork_buf\")")).to_equal(true)
```

</details>

#### capture limit is fixed at four MiB per stream

- capture limit is fixed at four MiB per stream
   - Expected: content contains `#define FORK_CAPTURE_LIMIT (4U * 1024U * 1024U)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("capture limit is fixed at four MiB per stream")
val content = rt_file_read_text("src/runtime/runtime_fork.c") ?? ""
expect(content.contains("#define FORK_CAPTURE_LIMIT (4U * 1024U * 1024U)")).to_equal(true)
```

</details>

#### buffer capture does not grow with child output

- buffer capture does not grow with child output
   - Expected: content does not contain `SPL_REALLOC(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("buffer capture does not grow with child output")
val content = rt_file_read_text("src/runtime/runtime_fork.c") ?? ""
expect(content.contains("SPL_REALLOC(")).to_equal(false)
```

</details>

#### truncated output reports the omitted byte count

- truncated output reports the omitted byte count
   - Expected: content contains `[output truncated: %llu bytes omitted]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("truncated output reports the omitted byte count")
val content = rt_file_read_text("src/runtime/runtime_fork.c") ?? ""
expect(content.contains("[output truncated: %llu bytes omitted]")).to_equal(true)
```

</details>

### WI-1: Fork result cleanup tracked

#### free_results uses SPL_FREE for stdout

- free_results uses SPL_FREE for stdout
   - Expected: content contains `SPL_FREE(s_result_stdout)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("free_results uses SPL_FREE for stdout")
val content = rt_file_read_text("src/runtime/runtime_fork.c") ?? ""
expect(content.contains("SPL_FREE(s_result_stdout)")).to_equal(true)
```

</details>

#### free_results uses SPL_FREE for stderr

- free_results uses SPL_FREE for stderr
   - Expected: content contains `SPL_FREE(s_result_stderr)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("free_results uses SPL_FREE for stderr")
val content = rt_file_read_text("src/runtime/runtime_fork.c") ?? ""
expect(content.contains("SPL_FREE(s_result_stderr)")).to_equal(true)
```

</details>

### WI-1: No raw malloc/free in fork functions

#### no raw malloc in rt_fork_parent_wait

- no raw malloc in rt_fork_parent_wait
   - Expected: raw_malloc_found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no raw malloc in rt_fork_parent_wait")
val content = rt_file_read_text("src/runtime/runtime_fork.c") ?? ""
val lines = content.split("\n")
var raw_malloc_found = false
for line in lines:
    val trimmed = line.trim()
    # Skip comment lines and emitted code strings
    if trimmed.starts_with("#") or trimmed.starts_with("//") or trimmed.starts_with("/*"):
        continue
    if (trimmed.contains("malloc(") and
        not trimmed.contains("SPL_MALLOC") and
        not trimmed.contains("SPL_CALLOC") and
        not trimmed.contains("SPL_REALLOC")):
        raw_malloc_found = true
expect(raw_malloc_found).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Memory Safety |
| Status | Active |
| Source | `test/unit/memleak/fork_alloc_tracking_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WI-1: runtime_fork.c includes memtrack header, WI-1: Fork buffer allocations tracked, WI-1: Fork result cleanup tracked, WI-1: No raw malloc/free in fork functions.
- WI-1: runtime_fork.c includes memtrack header
- WI-1: Fork buffer allocations tracked
- WI-1: Fork result cleanup tracked
- WI-1: No raw malloc/free in fork functions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `744632794944ab377ec1febc7431fbd5910258bcadcc939feb2df444c23bfed1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `744632794944ab377ec1febc7431fbd5910258bcadcc939feb2df444c23bfed1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `744632794944ab377ec1febc7431fbd5910258bcadcc939feb2df444c23bfed1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/memleak/fork_alloc_tracking_spec.spl
mirror: doc/06_spec/unit/memleak/fork_alloc_tracking_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/memleak/fork_alloc_tracking_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/memleak/fork_alloc_tracking_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/memleak/fork_alloc_tracking_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes runtime_memtrack.h' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/memleak/fork_alloc_tracking_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'buffer capture does not grow with child output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/memleak/fork_alloc_tracking_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'truncated output reports the omitted byte count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
