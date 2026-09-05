# Bitfield Reorder Specification

> <details>

<!-- sdn-diagram:id=bitfield_reorder_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bitfield_reorder_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bitfield_reorder_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bitfield_reorder_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bitfield Reorder Specification

## Scenarios

### Bitfield field reorder — attribute parsing

#### LayoutAttr has is_preserve_order and is_compactq fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/30.types/type_layout.spl")
expect(src.contains("is_preserve_order: bool")).to_equal(true)
expect(src.contains("is_compactq: bool")).to_equal(true)
```

</details>

#### parse_layout_attrs recognises @preserve_order

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/00.common/attributes.spl")
expect(src.contains("attr.name == \"preserve_order\"")).to_equal(true)
expect(src.contains("is_preserve_order = true")).to_equal(true)
```

</details>

#### parse_layout_attrs recognises @compactq

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/00.common/attributes.spl")
expect(src.contains("attr.name == \"compactq\"")).to_equal(true)
expect(src.contains("is_compactq = true")).to_equal(true)
```

</details>

#### @repr(C) implies preserve_order in attribute parser

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/00.common/attributes.spl")
expect(src.contains("layout_kind = LayoutKind.C")).to_equal(true)
expect(src.contains("is_preserve_order = true")).to_equal(true)
```

</details>

#### @repr(C) factory sets preserve_order true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/30.types/type_layout.spl")
expect(src.contains("layout_kind: LayoutKind.C")).to_equal(true)
expect(src.contains("is_preserve_order: true")).to_equal(true)
```

</details>

### Bitfield field reorder — backend logic

#### defines sort_fields_by_width_desc function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/70.backend/bitfield.spl")
expect(src.contains("fn sort_fields_by_width_desc")).to_equal(true)
```

</details>

#### defines would_straddle_word function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/70.backend/bitfield.spl")
expect(src.contains("fn would_straddle_word")).to_equal(true)
```

</details>

#### compile_bitfield accepts preserve_order and compactq params

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/70.backend/bitfield.spl")
expect(src.contains("preserve_order: bool")).to_equal(true)
expect(src.contains("compactq: bool")).to_equal(true)
expect(src.contains("target_word_bits: i64")).to_equal(true)
```

</details>

#### compile_bitfield calls sort when not preserve_order

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/70.backend/bitfield.spl")
expect(src.contains("if not preserve_order")).to_equal(true)
expect(src.contains("sort_fields_by_width_desc")).to_equal(true)
```

</details>

#### compile_bitfield checks word straddle when not compactq

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/70.backend/bitfield.spl")
expect(src.contains("if not compactq")).to_equal(true)
expect(src.contains("would_straddle_word")).to_equal(true)
```

</details>

### Bitfield field reorder — HIR lowering

#### lower_bitfield parses layout attrs from bitfield attributes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/20.hir/hir_lowering/items.spl")
expect(src.contains("parse_layout_attrs(bf.attributes)")).to_equal(true)
```

</details>

#### lower_bitfield sorts fields by width descending

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/20.hir/hir_lowering/items.spl")
expect(src.contains("widths[indices[j - 1]] < widths[indices[j]]")).to_equal(true)
```

</details>

#### lower_bitfield respects is_preserve_order

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/20.hir/hir_lowering/items.spl")
expect(src.contains("not layout_attr.is_preserve_order")).to_equal(true)
```

</details>

#### lower_bitfield avoids word straddle unless compactq

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/20.hir/hir_lowering/items.spl")
expect(src.contains("not layout_attr.is_compactq")).to_equal(true)
expect(src.contains("word_end")).to_equal(true)
```

</details>

### Bitfield field reorder — layoutattr factory defaults

#### layoutattr_default_ has preserve_order false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/30.types/type_layout.spl")
expect(src.contains("is_preserve_order: false")).to_equal(true)
expect(src.contains("is_compactq: false")).to_equal(true)
```

</details>

#### layoutattr_c_repr has preserve_order true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/30.types/type_layout.spl")
expect(src.contains("is_preserve_order: true")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/bitfield_reorder_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Bitfield field reorder — attribute parsing
- Bitfield field reorder — backend logic
- Bitfield field reorder — HIR lowering
- Bitfield field reorder — layoutattr factory defaults

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
