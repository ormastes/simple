# Entity Structure Specification

> <details>

<!-- sdn-diagram:id=entity_structure_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=entity_structure_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

entity_structure_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=entity_structure_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Entity Structure Specification

## Scenarios

### Entity Dimension Structure

#### keeps feature transform entity view surfaces available

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lexing = entity_view("lexing_to_parsing")
val parsing = entity_view("parsing_to_desugaring")
val typing = entity_view("typing_to_hir")
val mir = entity_view("mir_to_backend")

expect(lexing).to_contain("export TokenStreamView")
expect(parsing).to_contain("export AstView")
expect(typing).to_contain("export TypedAstView")
expect(mir).to_contain("export MirProgram")
expect(mir).to_contain("export MirDebugInfo")
```

</details>

#### keeps dimension defaults aligned with explicit entity view surfaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = dimension_def_source()

expect(source).to_contain("struct DimensionDef:")
expect(source).to_contain("surface_file: \"__init__.spl\"")
expect(source).to_contain("participation: \"explicit_bind_only\"")
expect(source).to_contain("intra_access: \"via_surface_only\"")
expect(source).to_contain("fn is_explicit_bind() -> bool")
expect(source).to_contain("fn rejects_cycles() -> bool")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/entity/entity_structure_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Entity Dimension Structure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
