# Ide Gui Harden Specification

> <details>

<!-- sdn-diagram:id=ide_gui_harden_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ide_gui_harden_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ide_gui_harden_spec -> std
ide_gui_harden_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ide_gui_harden_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ide Gui Harden Specification

## Scenarios

### gui_sanity: headless degradation — bounds and config checks

#### gui backend config has positive width (sane default even in headless)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ide_gui_bounds_valid()).to_equal(true)
```

</details>

#### ide_gui_sanity returns a result without crashing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sanity = ide_gui_sanity()
expect(sanity.theme.len() >= 0).to_equal(true)
```

</details>

#### gui config width is positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sanity = ide_gui_sanity()
expect(sanity.width > 0).to_equal(true)
```

</details>

#### gui config height is positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sanity = ide_gui_sanity()
expect(sanity.height > 0).to_equal(true)
```

</details>

#### gui sanity has_backend_config is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sanity = ide_gui_sanity()
expect(sanity.has_backend_config).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ide/ide_gui_harden_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gui_sanity: headless degradation — bounds and config checks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
