# Ide Capabilities Harden Specification

> <details>

<!-- sdn-diagram:id=ide_capabilities_harden_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ide_capabilities_harden_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ide_capabilities_harden_spec -> std
ide_capabilities_harden_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ide_capabilities_harden_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ide Capabilities Harden Specification

## Scenarios

### capabilities: all registered entries have valid required fields

#### all capabilities pass ide_capability_valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ide_capability_valid_count()).to_equal(ide_capability_count())
```

</details>

#### preview bounds with positive width and height are valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ide_preview_bounds_valid(800, 600)).to_equal(true)
```

</details>

#### preview bounds with zero width are invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ide_preview_bounds_valid(0, 600)).to_equal(false)
```

</details>

#### preview bounds with zero height are invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ide_preview_bounds_valid(800, 0)).to_equal(false)
```

</details>

#### preview bounds with negative dimensions are invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ide_preview_bounds_valid(-1, -1)).to_equal(false)
```

</details>

#### capability count is positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ide_capability_count() > 0).to_equal(true)
```

</details>

#### capability ids are all non-empty via ide_capability_valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var all_ok = true
for cap in ide_capabilities():
    if not ide_capability_valid(cap):
        all_ok = false
expect(all_ok).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ide/ide_capabilities_harden_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- capabilities: all registered entries have valid required fields

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
