# Symbol Specification

> <details>

<!-- sdn-diagram:id=symbol_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=symbol_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

symbol_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=symbol_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Symbol Specification

## Scenarios

### Symbol

#### keeps dependency symbol table data model available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = symbol_source()

expect(source).to_contain("enum SymbolKind:")
expect(source).to_contain("struct SymbolEntry:")
expect(source).to_contain("struct SymbolConflictError:")
expect(source).to_contain("struct SymbolTable:")
expect(source).to_contain("fn symbolconflicterror_new(name: text, existing: text, new_sym: text) -> SymbolConflictError")
expect(source).to_contain("fn symboltable_new(module_path: text) -> SymbolTable")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/interpreter/symbol_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Symbol

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
