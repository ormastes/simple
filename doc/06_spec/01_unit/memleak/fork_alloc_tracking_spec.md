# Fork Alloc Tracking Specification

> <details>

<!-- sdn-diagram:id=fork_alloc_tracking_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fork_alloc_tracking_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fork_alloc_tracking_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fork_alloc_tracking_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fork Alloc Tracking Specification

## Scenarios

### WI-1: runtime_fork.c includes memtrack header

#### includes runtime_memtrack.h

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_fork.c") ?? ""
expect(content.contains("#include \"runtime_memtrack.h\"")).to_equal(true)
```

</details>

### WI-1: Fork buffer allocations tracked

#### stdout buffer uses SPL_MALLOC with fork_buf tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_fork.c") ?? ""
expect(content.contains("SPL_MALLOC(out_cap, \"fork_buf\")")).to_equal(true)
```

</details>

#### stderr buffer uses SPL_MALLOC with fork_buf tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_fork.c") ?? ""
expect(content.contains("SPL_MALLOC(err_cap, \"fork_buf\")")).to_equal(true)
```

</details>

#### buffer fallback uses SPL_CALLOC

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_fork.c") ?? ""
expect(content.contains("SPL_CALLOC(1, 1, \"fork_buf\")")).to_equal(true)
```

</details>

#### buffer growth uses SPL_REALLOC

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_fork.c") ?? ""
expect(content.contains("SPL_REALLOC(*buf_ptr, *cap_ptr, \"fork_buf\")")).to_equal(true)
```

</details>

### WI-1: Fork result cleanup tracked

#### free_results uses SPL_FREE for stdout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_fork.c") ?? ""
expect(content.contains("SPL_FREE(s_result_stdout)")).to_equal(true)
```

</details>

#### free_results uses SPL_FREE for stderr

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_fork.c") ?? ""
expect(content.contains("SPL_FREE(s_result_stderr)")).to_equal(true)
```

</details>

### WI-1: No raw malloc/free in fork functions

#### no raw malloc in rt_fork_parent_wait

1. not trimmed contains
2. not trimmed contains
3. not trimmed contains
   - Expected: raw_malloc_found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/memleak/fork_alloc_tracking_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WI-1: runtime_fork.c includes memtrack header
- WI-1: Fork buffer allocations tracked
- WI-1: Fork result cleanup tracked
- WI-1: No raw malloc/free in fork functions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
