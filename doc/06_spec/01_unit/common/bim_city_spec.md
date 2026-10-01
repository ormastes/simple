# Bim City Specification

> Tests covering bim{} standards binding, city{} standards binding.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bim City Specification

## Scenarios

### bim{} standards binding

#### defines building, level, space, wall, material, and property-set bindings

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines building, level, space, wall, material, and property-set bindings
   - Expected: model.building equals `Demo Tower`
   - Expected: model.level equals `Level 1`
   - Expected: model.space equals `Room 101`
   - Expected: model.wall equals `North Wall`
   - Expected: model.material equals `Concrete`
   - Expected: model.property_sets.len() equals `1`
   - Expected: bim_model_complete(model) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("defines building, level, space, wall, material, and property-set bindings")
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

- validates explicit IFC and bSDD fixture identifiers
   - Expected: bim_validate_fixture_ids(model) is true
   - Expected: bim_validate_fixture_ids(bad) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("validates explicit IFC and bSDD fixture identifiers")
val model = sample_bim()
var bad = bim_model("Demo Tower", "Building")
bad = bim_model_add_property_set(bad, bim_property_set("Pset", "bad-id"))

expect(bim_validate_fixture_ids(model)).to_equal(true)
expect(bim_validate_fixture_ids(bad)).to_equal(false)
```

</details>

#### exports a gbXML conformance fixture

- exports a gbXML conformance fixture
   - Expected: gbxml_fixture_valid(xml) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("exports a gbXML conformance fixture")
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

- defines city object identity, LOD metadata, and CityGML target mapping
   - Expected: city_validate_fixture(model) is true
   - Expected: model.objects[0].identity equals `building-1`
   - Expected: model.objects[0].lod equals `2`
   - Expected: model.objects[0].citygml_target equals `bldg:Building`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("defines city object identity, LOD metadata, and CityGML target mapping")
var model = city_model("Demo City")
model = city_model_add_object(model, city_object("building-1", "2", "bldg:Building"))

expect(city_validate_fixture(model)).to_equal(true)
expect(model.objects[0].identity).to_equal("building-1")
expect(model.objects[0].lod).to_equal("2")
expect(model.objects[0].citygml_target).to_equal("bldg:Building")
```

</details>

#### exports a CityGML conformance fixture

- exports a CityGML conformance fixture
   - Expected: citygml_fixture_valid(xml) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("exports a CityGML conformance fixture")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bim{} standards binding, city{} standards binding.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMMON`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8946baaab0fd28623c9d07287631df7872a7e709451162fa00c89f0c6bbe71c6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8946baaab0fd28623c9d07287631df7872a7e709451162fa00c89f0c6bbe71c6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8946baaab0fd28623c9d07287631df7872a7e709451162fa00c89f0c6bbe71c6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/common/bim_city_spec.spl
mirror: doc/06_spec/01_unit/common/bim_city_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/common/bim_city_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/common/bim_city_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/common/bim_city_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/common/bim_city_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines building, level, space, wall, material, and property-set bindings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/bim_city_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates explicit IFC and bSDD fixture identifiers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/bim_city_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports a gbXML conformance fixture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
