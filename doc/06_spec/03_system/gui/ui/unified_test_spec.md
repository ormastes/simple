# Unified Test Specification

> <details>

<!-- sdn-diagram:id=unified_test_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unified_test_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unified_test_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unified_test_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unified Test Specification

## Scenarios

### Unified UI test portable smoke

#### records supported surfaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val surfaces = ["web", "tui_web"]
expect(surfaces.len()).to_equal(2)
expect(surfaces[0]).to_equal("web")
```

</details>

#### records shared fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture = "test/fixtures/ui/test_app.ui.sdn"
expect(fixture).to_end_with(".ui.sdn")
```

</details>

#### records semantic checks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checks = ["ready", "elements", "actions"]
expect(checks.len()).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/ui/unified_test_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Unified UI test portable smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
