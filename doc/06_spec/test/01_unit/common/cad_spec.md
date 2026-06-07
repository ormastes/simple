# Cad Specification

> <details>

<!-- sdn-diagram:id=cad_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cad_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cad_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cad_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cad Specification

## Scenarios

### cad{} parametric part authoring

#### supports primitives, transforms, holes, fillets, and parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val part = sample_part()

expect(part.name).to_equal("bracket")
expect(part.parameters.len()).to_equal(1)
expect(part.primitives.len()).to_equal(1)
expect(part.features.len()).to_equal(2)
expect(part.features[0].kind).to_equal("hole")
expect(part.features[1].kind).to_equal("fillet")
expect(part.transform.tz).to_equal(3.0)
expect(cad_part_complete(part)).to_equal(true)
```

</details>

### cad{} assembly authoring

#### expresses references and constraints

1. var assembly = cad assembly
2. assembly = cad assembly add ref
3. assembly = cad assembly add ref
4. assembly = cad assembly add constraint
   - Expected: cad_assembly_complete(assembly) is true
   - Expected: assembly.references.len() equals `2`
   - Expected: assembly.constraints.len() equals `1`
   - Expected: assembly.constraints[0].kind equals `distance`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var assembly = cad_assembly("fixture")
assembly = cad_assembly_add_ref(assembly, cad_assembly_ref("left_bracket", "bracket", cad_identity_transform()))
assembly = cad_assembly_add_ref(assembly, cad_assembly_ref("right_bracket", "bracket", cad_transform(100.0, 0.0, 0.0, 0.0, 0.0, 0.0)))
assembly = cad_assembly_add_constraint(assembly, cad_constraint("distance", "left_bracket", "right_bracket", 100.0))

expect(cad_assembly_complete(assembly)).to_equal(true)
expect(assembly.references.len()).to_equal(2)
expect(assembly.constraints.len()).to_equal(1)
expect(assembly.constraints[0].kind).to_equal("distance")
```

</details>

### STEP AP242 fixture export

#### exports representative part fixtures

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val step = cad_part_to_step_ap242_fixture(sample_part())

expect(step_ap242_fixture_valid(step)).to_equal(true)
expect(step).to_contain("PRODUCT('bracket'")
expect(step).to_contain("GEOMETRIC_REPRESENTATION_ITEM('box:body")
expect(step).to_contain("FEATURE_DEFINITION('hole:body")
expect(step).to_contain("FEATURE_DEFINITION('fillet:body")
```

</details>

#### exports representative assembly fixtures

1. var assembly = cad assembly
2. assembly = cad assembly add ref
3. assembly = cad assembly add constraint
   - Expected: step_ap242_fixture_valid(step) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var assembly = cad_assembly("fixture")
assembly = cad_assembly_add_ref(assembly, cad_assembly_ref("left_bracket", "bracket", cad_identity_transform()))
assembly = cad_assembly_add_constraint(assembly, cad_constraint("fixed", "left_bracket", "origin", 0.0))
val step = cad_assembly_to_step_ap242_fixture(assembly)

expect(step_ap242_fixture_valid(step)).to_equal(true)
expect(step).to_contain("NEXT_ASSEMBLY_USAGE_OCCURRENCE('left_bracket'")
expect(step).to_contain("GEOMETRIC_CONSTRAINT('fixed:left_bracket:origin:0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/cad_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- cad{} parametric part authoring
- cad{} assembly authoring
- STEP AP242 fixture export

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
