# Macro Import Minimal Specification

> 1. expect kind is macro

<!-- sdn-diagram:id=macro_import_minimal_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macro_import_minimal_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macro_import_minimal_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macro_import_minimal_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Macro Import Minimal Specification

## Scenarios

### SymKind

#### predicates

#### Macro is_macro returns true

1. expect kind is macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = SymKind.MacroKind
expect kind.is_macro()
```

</details>

#### ValueOrType is_macro returns false

1. expect not kind is macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = SymKind.ValueOrType
expect not kind.is_macro()
```

</details>

### MacroSymbol basic

#### creates value symbol

1. expect not sym kind is macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym = MacroSymbol.value_sym("mod", "foo")
val sym_kind = sym.get_kind()
expect not sym_kind.is_macro()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/dependency/macro_import_minimal_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SymKind
- MacroSymbol basic

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
