# Alloc Listener Specification

> <details>

<!-- sdn-diagram:id=alloc_listener_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=alloc_listener_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

alloc_listener_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=alloc_listener_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Alloc Listener Specification

## Scenarios

### WI-2: Allocation listener types in header

#### SplAllocEventKind enum defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_memtrack.h") ?? ""
expect(content.contains("SplAllocEventKind")).to_equal(true)
```

</details>

#### SPL_ALLOC_MALLOC defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_memtrack.h") ?? ""
expect(content.contains("SPL_ALLOC_MALLOC")).to_equal(true)
```

</details>

#### SPL_ALLOC_FREE defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_memtrack.h") ?? ""
expect(content.contains("SPL_ALLOC_FREE")).to_equal(true)
```

</details>

#### SplAllocEvent struct defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_memtrack.h") ?? ""
expect(content.contains("SplAllocEvent")).to_equal(true)
```

</details>

#### SplAllocEvent has kind field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_memtrack.h") ?? ""
expect(content.contains("SplAllocEventKind kind")).to_equal(true)
```

</details>

#### SplAllocEvent has ptr field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_memtrack.h") ?? ""
expect(content.contains("void*       ptr")).to_equal(true)
```

</details>

#### SplAllocEvent has alloc_id field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_memtrack.h") ?? ""
expect(content.contains("int64_t     alloc_id")).to_equal(true)
```

</details>

### WI-2: Listener callback typedef

#### spl_alloc_listener_fn typedef defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_memtrack.h") ?? ""
expect(content.contains("spl_alloc_listener_fn")).to_equal(true)
```

</details>

#### set_listener function declared

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_memtrack.h") ?? ""
expect(content.contains("spl_memtrack_set_listener")).to_equal(true)
```

</details>

#### clear_listener function declared

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_memtrack.h") ?? ""
expect(content.contains("spl_memtrack_clear_listener")).to_equal(true)
```

</details>

### WI-2: Listener implementation

#### g_listener_fn static variable exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_memtrack.c") ?? ""
expect(content.contains("g_listener_fn")).to_equal(true)
```

</details>

#### g_listener_data static variable exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_memtrack.c") ?? ""
expect(content.contains("g_listener_data")).to_equal(true)
```

</details>

#### record() dispatches to listener

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_memtrack.c") ?? ""
# spl_memtrack_record should call g_listener_fn when set
expect(content.contains("g_listener_fn(&ev, g_listener_data)")).to_equal(true)
```

</details>

#### unrecord() dispatches to listener before removing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_memtrack.c") ?? ""
# spl_memtrack_unrecord should notify listener with SPL_ALLOC_FREE
expect(content.contains("ev.kind     = SPL_ALLOC_FREE")).to_equal(true)
```

</details>

#### set_listener implementation exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_memtrack.c") ?? ""
expect(content.contains("void spl_memtrack_set_listener")).to_equal(true)
```

</details>

#### clear_listener sets to NULL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/runtime/runtime_memtrack.c") ?? ""
expect(content.contains("void spl_memtrack_clear_listener")).to_equal(true)
```

</details>

### WI-2: Simple FFI wrappers

#### mem_tracker/mod.spl exports listener functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/lib/nogc_sync_mut/mem_tracker/mod.spl") ?? ""
expect(content.contains("mem_set_listener")).to_equal(true)
expect(content.contains("mem_clear_listener")).to_equal(true)
```

</details>

#### extern declaration for set_listener

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/lib/nogc_sync_mut/mem_tracker/mod.spl") ?? ""
expect(content.contains("extern fn spl_memtrack_set_listener")).to_equal(true)
```

</details>

#### extern declaration for clear_listener

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/lib/nogc_sync_mut/mem_tracker/mod.spl") ?? ""
expect(content.contains("extern fn spl_memtrack_clear_listener")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Memory Safety |
| Status | Active |
| Source | `test/01_unit/memleak/alloc_listener_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
