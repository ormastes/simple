# World Units Importers Specification

> <details>

<!-- sdn-diagram:id=world_units_importers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=world_units_importers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

world_units_importers_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=world_units_importers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# World Units Importers Specification

## Scenarios

### World unit importers

#### imports required standard-backed seed rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = import_all_world_unit_seed_rows()
val sdn = imported_rows_to_sdn(rows)
expect(rows.len()).to_equal(10)
expect(imported_rows_have_unique_ids(rows)).to_equal(true)
expect(sdn).to_contain("source: \"UCUM\"")
expect(sdn).to_contain("source: \"ISO 4217/SIX\"")
expect(sdn).to_contain("source: \"UNECE Rec 20\"")
expect(sdn).to_contain("source: \"IUPAC Gold Book\"")
expect(sdn).to_contain("source: \"IEC 80000-13\"")
expect(sdn).to_contain("symbol: \"KiB\"")
expect(sdn).to_contain("code: \"DZN\"")
expect(sdn).to_contain("code: \"840\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/units/generators/world_units_importers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- World unit importers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
