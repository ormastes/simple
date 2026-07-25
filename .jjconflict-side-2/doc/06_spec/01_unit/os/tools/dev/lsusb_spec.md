# lsusb PCI Class Filter Specification

> Verifies that `is_usb_controller` correctly identifies USB host controllers by PCI class 0x0C and subclass 0x03, and rejects other class/subclass pairs.

<!-- sdn-diagram:id=lsusb_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lsusb_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lsusb_spec -> std
lsusb_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lsusb_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lsusb PCI Class Filter Specification

Verifies that `is_usb_controller` correctly identifies USB host controllers by PCI class 0x0C and subclass 0x03, and rejects other class/subclass pairs.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Tooling |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/01_unit/os/tools/dev/lsusb_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that `is_usb_controller` correctly identifies USB host controllers
by PCI class 0x0C and subclass 0x03, and rejects other class/subclass pairs.

## Scenarios

### is_usb_controller PCI class filter

#### accepts class 0x0C subclass 0x03 as a USB controller

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_usb_controller(0x0C, 0x03)
expect(result).to_equal(true)
```

</details>

#### rejects class 0x01 (mass storage) as not USB

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_usb_controller(0x01, 0x06)
expect(result).to_equal(false)
```

</details>

#### rejects class 0x0C with wrong subclass as not USB

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_usb_controller(0x0C, 0x00)
expect(result).to_equal(false)
```

</details>

#### rejects class 0x02 (network) as not USB

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_usb_controller(0x02, 0x00)
expect(result).to_equal(false)
```

</details>

#### rejects class 0x03 (display) as not USB

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_usb_controller(0x03, 0x00)
expect(result).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
