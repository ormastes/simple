# Runtime Family Specification

> <details>

<!-- sdn-diagram:id=runtime_family_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=runtime_family_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

runtime_family_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=runtime_family_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Runtime Family Specification

## Scenarios

### Runtime Family Integration

#### target preset — baremetal

#### baremetal allowed families has exactly two entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families = baremetal_allowed_families()
expect(families.len()).to_equal(2)
```

</details>

#### baremetal allowed families contains nogc_async_mut_noalloc

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families = baremetal_allowed_families()
expect(families[0]).to_equal("nogc_async_mut_noalloc")
```

</details>

#### baremetal allowed families contains common

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families = baremetal_allowed_families()
expect(families[1]).to_equal("common")
```

</details>

#### baremetal blocks gc_async_mut

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families = baremetal_allowed_families()
expect(is_family_allowed(families, "gc_async_mut")).to_equal(false)
```

</details>

#### baremetal blocks nogc_sync_mut

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families = baremetal_allowed_families()
expect(is_family_allowed(families, "nogc_sync_mut")).to_equal(false)
```

</details>

#### baremetal allows nogc_async_mut_noalloc

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families = baremetal_allowed_families()
expect(is_family_allowed(families, "nogc_async_mut_noalloc")).to_equal(true)
```

</details>

#### baremetal allows common

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families = baremetal_allowed_families()
expect(is_family_allowed(families, "common")).to_equal(true)
```

</details>

#### target preset — hosted

#### hosted allowed families is empty (no restriction)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families = hosted_allowed_families()
expect(families.len()).to_equal(0)
```

</details>

#### hosted allows gc_async_mut (empty list = no restriction)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families = hosted_allowed_families()
expect(is_family_allowed(families, "gc_async_mut")).to_equal(true)
```

</details>

#### hosted allows nogc_sync_mut

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families = hosted_allowed_families()
expect(is_family_allowed(families, "nogc_sync_mut")).to_equal(true)
```

</details>

#### hosted allows nogc_async_mut_noalloc

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families = hosted_allowed_families()
expect(is_family_allowed(families, "nogc_async_mut_noalloc")).to_equal(true)
```

</details>

#### target preset — embedded_with_heap

#### embedded_with_heap allowed families has exactly four entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families = embedded_with_heap_allowed_families()
expect(families.len()).to_equal(4)
```

</details>

#### embedded_with_heap contains nogc_async_mut_noalloc

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families = embedded_with_heap_allowed_families()
expect(families[0]).to_equal("nogc_async_mut_noalloc")
```

</details>

#### embedded_with_heap contains nogc_sync_mut

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families = embedded_with_heap_allowed_families()
expect(families[1]).to_equal("nogc_sync_mut")
```

</details>

#### embedded_with_heap contains nogc_async_mut

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families = embedded_with_heap_allowed_families()
expect(families[2]).to_equal("nogc_async_mut")
```

</details>

#### embedded_with_heap contains common

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families = embedded_with_heap_allowed_families()
expect(families[3]).to_equal("common")
```

</details>

#### embedded_with_heap blocks gc_async_mut

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families = embedded_with_heap_allowed_families()
expect(is_family_allowed(families, "gc_async_mut")).to_equal(false)
```

</details>

#### is_family_allowed helper

#### returns true when restriction list is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families: [text] = []
expect(is_family_allowed(families, "gc_async_mut")).to_equal(true)
```

</details>

#### returns true for any family when list is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families: [text] = []
expect(is_family_allowed(families, "nogc_sync_mut")).to_equal(true)
```

</details>

#### returns true for listed family

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families = ["nogc_async_mut_noalloc", "common"]
expect(is_family_allowed(families, "nogc_async_mut_noalloc")).to_equal(true)
```

</details>

#### returns false for non-listed family

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families = ["nogc_async_mut_noalloc", "common"]
expect(is_family_allowed(families, "gc_async_mut")).to_equal(false)
```

</details>

#### returns false for another non-listed family

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families = ["nogc_async_mut_noalloc", "common"]
expect(is_family_allowed(families, "nogc_sync_mut")).to_equal(false)
```

</details>

#### gc_mode_from_family_prefix

#### nogc_sync_mut prefix maps to nogc mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_gc_mode_from_prefix("nogc_sync_mut.fs")).to_equal("nogc")
```

</details>

#### nogc_async_mut prefix maps to nogc mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_gc_mode_from_prefix("nogc_async_mut.thread")).to_equal("nogc")
```

</details>

#### nogc_async_mut_noalloc prefix maps to nogc mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_gc_mode_from_prefix("nogc_async_mut_noalloc.exec")).to_equal("nogc")
```

</details>

#### gc_async_mut prefix maps to gc mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_gc_mode_from_prefix("gc_async_mut.alloc")).to_equal("gc")
```

</details>

#### common prefix maps to gc mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_gc_mode_from_prefix("common.text")).to_equal("gc")
```

</details>

#### std. prefixed nogc path maps to nogc mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_gc_mode_from_prefix("std.nogc_sync_mut.fs")).to_equal("nogc")
```

</details>

#### unknown prefix maps to unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_gc_mode_from_prefix("mylib.foo")).to_equal("unknown")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/runtime_family_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Runtime Family Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
