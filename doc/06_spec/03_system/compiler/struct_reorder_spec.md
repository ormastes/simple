# Struct Reorder Specification

> <details>

<!-- sdn-diagram:id=struct_reorder_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=struct_reorder_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

struct_reorder_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=struct_reorder_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Struct Reorder Specification

## Scenarios

### Struct field reorder — Simple layout functions

#### defines reorder_fields_by_size function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/30.types/type_layout.spl")
expect(src.contains("fn reorder_fields_by_size(fields: [HirField]) -> [HirField]")).to_equal(true)
```

</details>

#### defines arch-aware reorder_fields_by_size_for_arch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/30.types/type_layout.spl")
expect(src.contains("fn reorder_fields_by_size_for_arch")).to_equal(true)
```

</details>

#### sorts by size descending using insertion sort

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/30.types/type_layout.spl")
expect(src.contains("sizes[indices[j - 1]] < sizes[indices[j]]")).to_equal(true)
```

</details>

### Struct field reorder — layout dispatch

#### Simple layout reorders fields when not preserve_order

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/30.types/type_layout.spl")
expect(src.contains("reorder_fields_by_size(fields)")).to_equal(true)
```

</details>

#### Simple layout skips reorder when preserve_order

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/30.types/type_layout.spl")
expect(src.contains("attr.is_preserve_order")).to_equal(true)
```

</details>

#### compactq uses packed layout with reordered fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/30.types/type_layout.spl")
expect(src.contains("attr.is_compactq")).to_equal(true)
expect(src.contains("compute_packed_layout")).to_equal(true)
```

</details>

#### C layout always preserves field order

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/30.types/type_layout.spl")
expect(src.contains("case LayoutKind.C")).to_equal(true)
```

</details>

### Struct field reorder — Rust seed

#### StructLayout has new_with_options method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler_rust/compiler/src/hir/types/layout.rs")
expect(src.contains("pub fn new_with_options")).to_equal(true)
```

</details>

#### new_with_options accepts preserve_order and compactq

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler_rust/compiler/src/hir/types/layout.rs")
expect(src.contains("preserve_order: bool")).to_equal(true)
expect(src.contains("compactq: bool")).to_equal(true)
```

</details>

#### Rust seed sorts fields by size descending

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler_rust/compiler/src/hir/types/layout.rs")
expect(src.contains("b.1.cmp(&a.1)")).to_equal(true)
```

</details>

#### Rust seed uses alignment 1 for compactq

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler_rust/compiler/src/hir/types/layout.rs")
expect(src.contains("effective_align = if compactq")).to_equal(true)
expect(src.contains("effective_max = if compactq")).to_equal(true)
```

</details>

#### new delegates to new_with_options with defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler_rust/compiler/src/hir/types/layout.rs")
expect(src.contains("Self::new_with_options(name, fields, registry, has_vtable, type_id, false, false)")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/struct_reorder_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Struct field reorder — Simple layout functions
- Struct field reorder — layout dispatch
- Struct field reorder — Rust seed

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
