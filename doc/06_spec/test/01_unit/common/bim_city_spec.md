# Bim City Specification

> <details>

<!-- sdn-diagram:id=bim_city_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bim_city_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bim_city_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bim_city_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bim City Specification

## Scenarios

### bim{} standards binding

#### defines building, level, space, wall, material, and property-set bindings

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = sample_bim()

expect(model.building).to_equal("Demo Tower")
expect(model.level).to_equal("Level 1")
expect(model.space).to_equal("Room 101")
expect(model.wall).to_equal("North Wall")
expect(model.material).to_equal("Concrete")
expect(model.property_sets.len()).to_equal(1)
expect(bim_model_complete(model)).to_equal(true)
```

</details>

#### validates explicit IFC and bSDD fixture identifiers

1. var bad = bim model
2. bad = bim model add property set
   - Expected: bim_validate_fixture_ids(model) is true
   - Expected: bim_validate_fixture_ids(bad) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = sample_bim()
var bad = bim_model("Demo Tower", "Building")
bad = bim_model_add_property_set(bad, bim_property_set("Pset", "bad-id"))

expect(bim_validate_fixture_ids(model)).to_equal(true)
expect(bim_validate_fixture_ids(bad)).to_equal(false)
```

</details>

#### exports a gbXML conformance fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xml = bim_to_gbxml_fixture(sample_bim())

expect(xml).to_contain("<gbXML version=\"7.03\"")
expect(xml).to_contain("<Building id=\"IfcBuilding\"")
expect(xml).to_contain("<Space id=\"Room_101\"")
expect(xml).to_contain("<Surface id=\"North_Wall\"")
expect(gbxml_fixture_valid(xml)).to_equal(true)
```

</details>

### city{} standards binding

#### defines city object identity, LOD metadata, and CityGML target mapping

1. var model = city model
2. model = city model add object
   - Expected: city_validate_fixture(model) is true
   - Expected: model.objects[0].identity equals `building-1`
   - Expected: model.objects[0].lod equals `2`
   - Expected: model.objects[0].citygml_target equals `bldg:Building`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var model = city_model("Demo City")
model = city_model_add_object(model, city_object("building-1", "2", "bldg:Building"))

expect(city_validate_fixture(model)).to_equal(true)
expect(model.objects[0].identity).to_equal("building-1")
expect(model.objects[0].lod).to_equal("2")
expect(model.objects[0].citygml_target).to_equal("bldg:Building")
```

</details>

#### exports a CityGML conformance fixture

1. var model = city model
2. model = city model add object
   - Expected: citygml_fixture_valid(xml) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var model = city_model("Demo City")
model = city_model_add_object(model, city_object("building-1", "2", "bldg:Building"))
val xml = city_to_citygml_fixture(model)

expect(xml).to_contain("<core:CityModel version=\"3.0\"")
expect(xml).to_contain("<bldg:Building gml:id=\"building-1\"")
expect(xml).to_contain("<core:lod>2</core:lod>")
expect(citygml_fixture_valid(xml)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/bim_city_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- bim{} standards binding
- city{} standards binding

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
