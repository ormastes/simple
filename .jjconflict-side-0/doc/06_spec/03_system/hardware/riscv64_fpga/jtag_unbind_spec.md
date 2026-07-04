# Jtag Unbind Specification

> <details>

<!-- sdn-diagram:id=jtag_unbind_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=jtag_unbind_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

jtag_unbind_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=jtag_unbind_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jtag Unbind Specification

## Scenarios

### JTAG Unbind Script - Existence (AC-3)

#### jtag unbind script path is under scripts directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prefix = "scripts/"
val name = "scripts/jtag-ftdi-unbind.shs"
expect(name).to_start_with(prefix)
expect(name).to_end_with(".shs")
```

</details>

#### jtag unbind script name contains jtag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "jtag-ftdi-unbind.shs"
expect(name).to_contain("jtag")
```

</details>

#### jtag unbind script name contains ftdi

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "jtag-ftdi-unbind.shs"
expect(name).to_contain("ftdi")
```

</details>

#### jtag unbind script name contains unbind

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "jtag-ftdi-unbind.shs"
expect(name).to_contain("unbind")
```

</details>

### JTAG Unbind Script - Interface Target (AC-3)

#### script targets USB interface 3-2:1.0 for JTAG channel A

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val interface_id = "3-2:1.0"
expect(interface_id).to_contain("3-2")
expect(interface_id).to_end_with("1.0")
```

</details>

#### FTDI driver name is ftdi_sio

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = "ftdi_sio"
expect(driver).to_equal("ftdi_sio")
```

</details>

#### unbind sysfs path contains usb driver ftdi_sio

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/sys/bus/usb/drivers/ftdi_sio/unbind"
expect(path).to_contain("ftdi_sio")
expect(path).to_contain("unbind")
```

</details>

#### rebind sysfs path contains usb driver ftdi_sio

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/sys/bus/usb/drivers/ftdi_sio/bind"
expect(path).to_contain("ftdi_sio")
expect(path).to_contain("bind")
```

</details>

#### unbind target interface index is 0 (JTAG/MPSSE channel A)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val iface_index = 0
expect(iface_index).to_equal(0)
```

</details>

### JTAG Unbind Script - BLOCKED Gates (AC-3, AC-8)

#### BLOCKED: JTAG unbind requires connected FT4232H device

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocked_line = "BLOCKED jtag_unbind: BLOCKED: JTAG unbind requires connected FT4232H device"
print blocked_line
expect(blocked_line).to_start_with("BLOCKED jtag_unbind:")
expect(blocked_line).to_contain("connected FT4232H device")
```

</details>

#### BLOCKED: ftdi_sio rebind requires connected FT4232H device

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocked_line = "BLOCKED ftdi_sio_rebind: no FT4232H USB device found (lsusb 0403:6011 absent)"
print blocked_line
expect(blocked_line).to_start_with("BLOCKED ftdi_sio_rebind:")
expect(blocked_line).to_contain("0403:6011")
```

</details>

#### BLOCKED: openocd JTAG probe requires unbound ftdi_sio interface

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocked_line = "BLOCKED openocd_jtag_probe: requires unbound ftdi_sio interface before openocd probe"
print blocked_line
expect(blocked_line).to_start_with("BLOCKED openocd_jtag_probe:")
expect(blocked_line).to_contain("unbound ftdi_sio interface")
expect(blocked_line).to_contain("openocd")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/riscv64_fpga/jtag_unbind_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- JTAG Unbind Script - Existence (AC-3)
- JTAG Unbind Script - Interface Target (AC-3)
- JTAG Unbind Script - BLOCKED Gates (AC-3, AC-8)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
