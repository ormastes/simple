# Trait Validation Symbol Shape Specification

> <details>

<!-- sdn-diagram:id=trait_validation_symbol_shape_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=trait_validation_symbol_shape_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

trait_validation_symbol_shape_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=trait_validation_symbol_shape_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Trait Validation Symbol Shape Specification

## Scenarios

### trait validation symbol shape

#### constructs built-in trait symbols with the full HIR Symbol shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/compiler/25.traits/trait_validation.spl")

expect(source).to_contain("fn builtin_trait_symbol(id: i64, name: text, span: Span) -> Symbol:")
expect(source).to_contain("id: SymbolId(id: id)")
expect(source).to_contain("kind: SymbolKind.Trait")
expect(source).to_contain("visibility: Visibility.Public")
expect(source).to_contain("TraitDef.create(builtin_trait_symbol(1, \"Clone\", dummy_span), dummy_span)")
expect(source).to_contain("copy_trait.supertraits = [builtin_trait_symbol(1, \"Clone\", dummy_span)]")
expect(source).to_not_contain("TraitDef.create(Symbol(id:")
expect(source).to_not_contain("supertraits = [Symbol(id:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/traits/trait_validation_symbol_shape_spec.spl` |
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- trait validation symbol shape

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
