# Hardware Check Specification

> <details>

<!-- sdn-diagram:id=hardware_check_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hardware_check_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hardware_check_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hardware_check_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hardware Check Specification

## Scenarios

### Hardware detection

#### st-info tool check

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val available = is_stlink_tools_available()
expect(available == true or available == false).to_equal(true)
```

</details>

#### T32 tool check

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val available = is_t32_available()
expect(available == true or available == false).to_equal(true)
```

</details>

#### T32 USB readiness check

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val available = is_t32_usb_ready()
expect(available == true or available == false).to_equal(true)
```

</details>

#### OpenOCD tool check

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val available = is_openocd_available()
expect(available == true or available == false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/debug/hardware/hardware_check_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Hardware detection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
