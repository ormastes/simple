# Thread Alloc Tracking Specification

> <details>

<!-- sdn-diagram:id=thread_alloc_tracking_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=thread_alloc_tracking_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

thread_alloc_tracking_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=thread_alloc_tracking_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Thread Alloc Tracking Specification

## Scenarios

### WI-1: runtime_thread.c includes memtrack header

#### includes runtime_memtrack.h

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("#include \"runtime_memtrack.h\"")).to_equal(true)
```

</details>

### WI-1: Thread allocations use SPL_MALLOC

#### thread create uses SPL_MALLOC for pthread_t

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("SPL_MALLOC(sizeof(pthread_t), \"thread\")")).to_equal(true)
```

</details>

#### thread create error path uses SPL_FREE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("SPL_FREE(thread)")).to_equal(true)
```

</details>

### WI-1: Mutex allocations use SPL_MALLOC

#### mutex create uses SPL_MALLOC for pthread_mutex_t

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("SPL_MALLOC(sizeof(pthread_mutex_t), \"mutex\")")).to_equal(true)
```

</details>

#### mutex error path uses SPL_FREE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("SPL_FREE(mutex)")).to_equal(true)
```

</details>

#### Windows mutex uses SPL_MALLOC with cs_mutex tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("SPL_MALLOC(sizeof(CRITICAL_SECTION), \"cs_mutex\")")).to_equal(true)
```

</details>

#### Windows mutex destroy uses SPL_FREE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("SPL_FREE(cs)")).to_equal(true)
```

</details>

### WI-1: Condvar allocations use SPL_MALLOC

#### condvar create uses SPL_MALLOC for pthread_cond_t

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("SPL_MALLOC(sizeof(pthread_cond_t), \"condvar\")")).to_equal(true)
```

</details>

#### condvar error path uses SPL_FREE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("SPL_FREE(cond)")).to_equal(true)
```

</details>

#### Windows condvar uses SPL_MALLOC with cv_condvar tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("SPL_MALLOC(sizeof(CONDITION_VARIABLE), \"cv_condvar\")")).to_equal(true)
```

</details>

#### Windows condvar destroy uses SPL_FREE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_thread.c") ?? ""
expect(content.contains("SPL_FREE(cv)")).to_equal(true)
```

</details>

### WI-1: No raw malloc/free in thread functions

#### thread_create has no raw malloc

1. not trimmed contains
   - Expected: raw_thread_malloc is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/memleak/thread_alloc_tracking_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
