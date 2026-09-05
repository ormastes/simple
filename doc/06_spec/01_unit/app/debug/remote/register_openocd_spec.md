# Register Openocd Specification

> <details>

<!-- sdn-diagram:id=register_openocd_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=register_openocd_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

register_openocd_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=register_openocd_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Register Openocd Specification

## Scenarios

### OpenOCD feature registration

#### registers execution control at rank NATIVE

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = openocd_registered_features()
val halt = features[0]
expect(halt.name).to_equal("Halt")
expect(halt.rank).to_equal(FeatureRank.NATIVE())
```

</details>

#### registers memory ops at rank NATIVE

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = openocd_registered_features()
val mem = features[3]
expect(mem.name).to_equal("ReadMemory")
expect(mem.rank).to_equal(0)
```

</details>

#### registers FlashProgram at rank NATIVE

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = openocd_registered_features()
val flash = features[5]
expect(flash.name).to_equal("FlashProgram")
expect(flash.rank).to_equal(0)
```

</details>

#### registers SystemReset at rank NATIVE

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = openocd_registered_features()
val reset = features[6]
expect(reset.name).to_equal("SystemReset")
expect(reset.rank).to_equal(0)
```

</details>

#### registers OpenocdMonitor at rank NATIVE

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = openocd_registered_features()
val mon = features[7]
expect(mon.name).to_equal("OpenocdMonitor")
expect(mon.rank).to_equal(0)
```

</details>

#### all features use openocd backend name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = openocd_registered_features()
for f in features:
    expect(f.backend).to_equal("openocd")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/register_openocd_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- OpenOCD feature registration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
