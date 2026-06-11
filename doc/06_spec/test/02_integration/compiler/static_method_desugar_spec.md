# Static Method Desugar Specification

> <details>

<!-- sdn-diagram:id=static_method_desugar_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=static_method_desugar_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

static_method_desugar_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=static_method_desugar_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static Method Desugar Specification

## Scenarios

### Static Method Desugaring

#### keeps HIR static method symbol support available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/compiler/20.hir/hir_types.spl") ?? ""

expect(source).to_contain("StaticMethod(type_id: SymbolId, method_id: SymbolId)")
expect(source).to_contain("Look up a static method in a class/struct/enum")
expect(source).to_contain("Static methods are defined with `static fn`")
```

</details>

#### keeps MIR lowering support for static method calls available

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/compiler/50.mir/mir_lowering_expr_part3.spl") ?? ""

expect(source).to_contain("case StaticMethod(type_id, method_id):")
expect(source).to_contain("method_id")
```

</details>

#### keeps frontend desugar module available

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/compiler/10.frontend/desugar/mod.spl") ?? ""

expect(source).to_contain("desugar")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/static_method_desugar_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Static Method Desugaring

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
