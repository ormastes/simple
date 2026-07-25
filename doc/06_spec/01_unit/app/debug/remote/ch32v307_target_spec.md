# Ch32v307 Target Specification

> <details>

<!-- sdn-diagram:id=ch32v307_target_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ch32v307_target_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ch32v307_target_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ch32v307_target_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ch32v307 Target Specification

## Scenarios

### Ch32v307Target defaults

#### has correct name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Ch32v307Target.default()
expect(t.name()).to_equal("CH32V307 (RV32IMAC+F)")
```

</details>

#### has correct WCH-Link serial

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Ch32v307Target.default()
expect(t.wlink_serial).to_equal("711A8F06F64D")
```

</details>

#### has correct chip ID

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Ch32v307Target.default()
expect(t.chip_id).to_equal("0x30700568")
```

</details>

#### has correct flash base and size

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Ch32v307Target.default()
expect(t.flash_base).to_equal(0x08000000)
expect(t.flash_size).to_equal(294912)
```

</details>

#### has correct RAM base and size

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Ch32v307Target.default()
expect(t.ram_base).to_equal(0x20000000)
expect(t.ram_size).to_equal(32768)
```

</details>

#### has correct ISA

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Ch32v307Target.default()
expect(t.isa).to_equal("RV32ACFIMUX")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/ch32v307_target_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Ch32v307Target defaults

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
