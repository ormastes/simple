# Ide Slides Harden Specification

> <details>

<!-- sdn-diagram:id=ide_slides_harden_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ide_slides_harden_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ide_slides_harden_spec -> std
ide_slides_harden_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ide_slides_harden_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ide Slides Harden Specification

## Scenarios

### slides_compat: empty presentation does not crash

#### empty presentation probe returns non-negative slide count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = ide_slide_compat_probe_empty()
expect(probe.slide_count >= 0).to_equal(true)
```

</details>

#### empty presentation outline_line_count is non-negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = ide_slide_compat_probe_empty()
expect(probe.outline_line_count >= 0).to_equal(true)
```

</details>

#### empty presentation design_count is non-negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = ide_slide_compat_probe_empty()
expect(probe.design_count >= 0).to_equal(true)
```

</details>

#### sample presentation has at least one slide

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = ide_slide_compat_probe()
expect(probe.slide_count > 0).to_equal(true)
```

</details>

#### sample presentation thumbnail is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = ide_slide_compat_probe()
expect(probe.thumbnail.len() > 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ide/ide_slides_harden_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- slides_compat: empty presentation does not crash

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
