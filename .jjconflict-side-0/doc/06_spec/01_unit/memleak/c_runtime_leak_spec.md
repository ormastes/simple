# C Runtime Leak Specification

> <details>

<!-- sdn-diagram:id=c_runtime_leak_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=c_runtime_leak_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

c_runtime_leak_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=c_runtime_leak_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# C Runtime Leak Specification

## Scenarios

### C Runtime Leak

#### keeps runtime allocation and free entrypoints declared

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = rt_file_read_text("src/runtime/runtime.h") ?? ""

expect(header).to_contain("void*    rt_alloc(int64_t size);")
expect(header).to_contain("void*    rt_realloc(void* ptr, int64_t size);")
expect(header).to_contain("void     rt_free(void* ptr);")
expect(header).to_contain("void*    spl_malloc(int64_t size);")
expect(header).to_contain("void     spl_free(void* ptr);")
```

</details>

#### keeps thread handle cleanup entrypoint declared

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = rt_file_read_text("src/runtime/runtime_thread.h") ?? ""

expect(header).to_contain("void    rt_thread_free(int64_t handle);")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Memory Safety |
| Status | Active |
| Source | `test/01_unit/memleak/c_runtime_leak_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- C Runtime Leak

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
