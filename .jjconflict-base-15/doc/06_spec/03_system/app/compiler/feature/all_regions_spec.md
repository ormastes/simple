# All Regions Specification

> <details>

<!-- sdn-diagram:id=all_regions_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=all_regions_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

all_regions_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=all_regions_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# All Regions Specification

## Scenarios

### all regions language strategy

### REQ-001: region map

#### keeps SDN as carrier rather than universal authoring surface

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn_primary = "config manifests metadata snapshots catalogs generated-ir"
expect(sdn_primary).to_contain("metadata")
```

</details>

### REQ-003: priority order

#### starts with schema and style/ui

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = "schema"
val second = "style/ui"
expect(first).to_equal("schema")
expect(second).to_equal("style/ui")
```

</details>

### REQ-004: interchange anchors

#### names standards for heavy domains

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val anchors = "MusicXML IFC bSDD gbXML CityGML STEP AP242 VHDL SystemVerilog"
expect(anchors).to_contain("MusicXML")
expect(anchors).to_contain("STEP AP242")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/all_regions_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- all regions language strategy
- REQ-001: region map
- REQ-003: priority order
- REQ-004: interchange anchors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
