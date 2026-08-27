# Thread Alloc Tracking Specification

> Tests covering WI-1: runtime_thread.c includes memtrack header, WI-1: Thread allocations use SPL_MALLOC, WI-1: Mutex allocations use SPL_MALLOC, WI-1: Condvar allocations use SPL_MALLOC, WI-1: No raw malloc/free in thread functions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Thread Alloc Tracking Specification

## Scenarios

### WI-1: runtime_thread.c includes memtrack header

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
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("#include \"runtime_memtrack.h\"")).to_equal(true)
```

</details>

### WI-1: Thread allocations use SPL_MALLOC

#### thread create uses SPL_MALLOC for pthread_t

- thread create uses SPL_MALLOC for pthread_t
   - Expected: content contains `SPL_MALLOC(sizeof(pthread_t), "thread")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("thread create uses SPL_MALLOC for pthread_t")
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("SPL_MALLOC(sizeof(pthread_t), \"thread\")")).to_equal(true)
```

</details>

#### thread create error path uses SPL_FREE

- thread create error path uses SPL_FREE
   - Expected: content contains `SPL_FREE(thread)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("thread create error path uses SPL_FREE")
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("SPL_FREE(thread)")).to_equal(true)
```

</details>

### WI-1: Mutex allocations use SPL_MALLOC

#### mutex create uses SPL_MALLOC for pthread_mutex_t

- mutex create uses SPL_MALLOC for pthread_mutex_t
   - Expected: content contains `SPL_MALLOC(sizeof(pthread_mutex_t), "mutex")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mutex create uses SPL_MALLOC for pthread_mutex_t")
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("SPL_MALLOC(sizeof(pthread_mutex_t), \"mutex\")")).to_equal(true)
```

</details>

#### mutex error path uses SPL_FREE

- mutex error path uses SPL_FREE
   - Expected: content contains `SPL_FREE(mutex)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mutex error path uses SPL_FREE")
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("SPL_FREE(mutex)")).to_equal(true)
```

</details>

#### Windows mutex uses SPL_MALLOC with cs_mutex tag

- Windows mutex uses SPL_MALLOC with cs_mutex tag
   - Expected: content contains `SPL_MALLOC(sizeof(CRITICAL_SECTION), "cs_mutex")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Windows mutex uses SPL_MALLOC with cs_mutex tag")
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("SPL_MALLOC(sizeof(CRITICAL_SECTION), \"cs_mutex\")")).to_equal(true)
```

</details>

#### Windows mutex destroy uses SPL_FREE

- Windows mutex destroy uses SPL_FREE
   - Expected: content contains `SPL_FREE(cs)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Windows mutex destroy uses SPL_FREE")
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("SPL_FREE(cs)")).to_equal(true)
```

</details>

### WI-1: Condvar allocations use SPL_MALLOC

#### condvar create uses SPL_MALLOC for pthread_cond_t

- condvar create uses SPL_MALLOC for pthread_cond_t
   - Expected: content contains `SPL_MALLOC(sizeof(pthread_cond_t), "condvar")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("condvar create uses SPL_MALLOC for pthread_cond_t")
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("SPL_MALLOC(sizeof(pthread_cond_t), \"condvar\")")).to_equal(true)
```

</details>

#### condvar error path uses SPL_FREE

- condvar error path uses SPL_FREE
   - Expected: content contains `SPL_FREE(cond)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("condvar error path uses SPL_FREE")
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("SPL_FREE(cond)")).to_equal(true)
```

</details>

#### Windows condvar uses SPL_MALLOC with cv_condvar tag

- Windows condvar uses SPL_MALLOC with cv_condvar tag
   - Expected: content contains `SPL_MALLOC(sizeof(CONDITION_VARIABLE), "cv_condvar")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Windows condvar uses SPL_MALLOC with cv_condvar tag")
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("SPL_MALLOC(sizeof(CONDITION_VARIABLE), \"cv_condvar\")")).to_equal(true)
```

</details>

#### Windows condvar destroy uses SPL_FREE

- Windows condvar destroy uses SPL_FREE
   - Expected: content contains `SPL_FREE(cv)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Windows condvar destroy uses SPL_FREE")
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("SPL_FREE(cv)")).to_equal(true)
```

</details>

### WI-1: No raw malloc/free in thread functions

#### thread_create has no raw malloc

- thread_create has no raw malloc
   - Expected: raw_thread_malloc is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("thread_create has no raw malloc")
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
# All malloc calls should be SPL_MALLOC, except in static init
# Verify pthread_t allocation is tracked
val lines = content.split("\n")
var raw_thread_malloc = false
for line in lines:
    val trimmed = line.trim()
    if (trimmed.contains("malloc(sizeof(pthread_t))") and
        not trimmed.contains("SPL_MALLOC")):
        raw_thread_malloc = true
expect(raw_thread_malloc).to_equal(false)
```

</details>

#### thread pool spawn also uses SPL_MALLOC

- thread pool spawn also uses SPL_MALLOC
   - Expected: count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("thread pool spawn also uses SPL_MALLOC")
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
# Count SPL_MALLOC for thread — should appear twice (create + pool_spawn)
var count = 0
val lines = content.split("\n")
for line in lines:
    if line.contains("SPL_MALLOC(sizeof(pthread_t), \"thread\")"):
        count = count + 1
expect(count).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Memory Safety |
| Status | Active |
| Source | `test/unit/memleak/thread_alloc_tracking_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WI-1: runtime_thread.c includes memtrack header, WI-1: Thread allocations use SPL_MALLOC, WI-1: Mutex allocations use SPL_MALLOC, WI-1: Condvar allocations use SPL_MALLOC, WI-1: No raw malloc/free in thread functions.
- WI-1: runtime_thread.c includes memtrack header
- WI-1: Thread allocations use SPL_MALLOC
- WI-1: Mutex allocations use SPL_MALLOC
- WI-1: Condvar allocations use SPL_MALLOC
- WI-1: No raw malloc/free in thread functions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `2d19e3024f8c6335ef61bc2695b83fb3089c8996aeee0fbb3af4b2557a500c68`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2d19e3024f8c6335ef61bc2695b83fb3089c8996aeee0fbb3af4b2557a500c68`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2d19e3024f8c6335ef61bc2695b83fb3089c8996aeee0fbb3af4b2557a500c68`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/memleak/thread_alloc_tracking_spec.spl
mirror: doc/06_spec/unit/memleak/thread_alloc_tracking_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/memleak/thread_alloc_tracking_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/memleak/thread_alloc_tracking_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/memleak/thread_alloc_tracking_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/memleak/thread_alloc_tracking_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes runtime_memtrack.h' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/memleak/thread_alloc_tracking_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'thread create uses SPL_MALLOC for pthread_t' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/memleak/thread_alloc_tracking_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'thread create error path uses SPL_FREE' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
