# Ide Sheets Harden Specification

> <details>

<!-- sdn-diagram:id=ide_sheets_harden_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ide_sheets_harden_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ide_sheets_harden_spec -> std
ide_sheets_harden_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ide_sheets_harden_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ide Sheets Harden Specification

## Scenarios

### sheets_compat: empty workbook and empty formula do not crash

#### empty workbook probe returns non-crashing result with correct app_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = ide_sheet_compat_probe_empty()
expect(probe.app_id).to_equal("sheets")
```

</details>

#### empty workbook used_range is safe (non-crash)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = ide_sheet_compat_probe_empty()
expect(probe.sample_range.len() >= 0).to_equal(true)
```

</details>

#### empty formula display text does not return #CRASH

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ide_sheet_compat_empty_formula_safe()).to_equal(true)
```

</details>

#### standard sheet probe formula_evaluator_ok is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = ide_sheet_compat_probe()
expect(probe.formula_evaluator_ok).to_equal(true)
```

</details>

#### standard sheet probe owner_module is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = ide_sheet_compat_probe()
expect(probe.owner_module.len() > 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ide/ide_sheets_harden_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- sheets_compat: empty workbook and empty formula do not crash

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
