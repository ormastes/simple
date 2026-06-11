# Gc Family Boundary Hook Specification

> <details>

<!-- sdn-diagram:id=gc_family_boundary_hook_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gc_family_boundary_hook_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gc_family_boundary_hook_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gc_family_boundary_hook_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Family Boundary Hook Specification

## Scenarios

### interpreter gc family boundary hook wiring

#### extracts noalloc before async mutable families

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _source()
val noalloc_pos = source.index_of("contains(\"/nogc_async_mut_noalloc/\")") ?? -1
val async_pos = source.index_of("contains(\"/nogc_async_mut/\")") ?? -1
expect(noalloc_pos).to_be_greater_than(-1)
expect(async_pos).to_be_greater_than(-1)
expect(noalloc_pos).to_be_less_than(async_pos)
```

</details>

#### skips unknown and common families before warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _source()
expect(source).to_contain("if importer_family == \"\" or imported_family == \"\":")
expect(source).to_contain("if importer_family == \"common\" or imported_family == \"common\":")
```

</details>

#### warns for no-gc importing gc

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _source()
expect(source).to_contain("if is_nogc_family(importer_family) and is_gc_family(imported_family):")
expect(source).to_contain("GC module")
expect(source).to_contain("eval_warnings.push(msg)")
expect(source).to_contain("print msg")
```

</details>

#### warns for noalloc importing allocating family

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _source()
expect(source).to_contain("if is_noalloc_family(importer_family) and is_allocating_family(imported_family):")
expect(source).to_contain("Allocating module")
expect(source).to_contain("print msg")
```

</details>

#### deduplicates warning keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _source()
expect(source).to_contain("val warn_key = importer_family + \">\" + imported_family + \":\" + module_name")
expect(source).to_contain("_gc_warn_emitted.has(warn_key)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/gc_family_boundary_hook_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- interpreter gc family boundary hook wiring

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
