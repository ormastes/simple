# Ide Launch Harden Specification

> <details>

<!-- sdn-diagram:id=ide_launch_harden_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ide_launch_harden_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ide_launch_harden_spec -> std
ide_launch_harden_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ide_launch_harden_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ide Launch Harden Specification

## Scenarios

### launch_sanity: empty argv and unknown option handling

#### empty argv parse does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ide_launch_empty_argv_safe()).to_equal(true)
```

</details>

#### unknown-only flag populates unknown_option not mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ide_launch_unknown_only()).to_equal(true)
```

</details>

#### launch sanity tui mode is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sanity = ide_launch_sanity()
expect(sanity.tui_mode.len() > 0).to_equal(true)
```

</details>

#### launch sanity bad mode populates unknown_option

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sanity = ide_launch_sanity()
expect(sanity.unknown_option.len() > 0).to_equal(true)
```

</details>

#### launch sanity file_count is non-negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sanity = ide_launch_sanity()
expect(sanity.file_count >= 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ide/ide_launch_harden_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- launch_sanity: empty argv and unknown option handling

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
