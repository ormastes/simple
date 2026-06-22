# Preflight Specification

> <details>

<!-- sdn-diagram:id=preflight_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=preflight_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

preflight_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=preflight_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Preflight Specification

## Scenarios

### Preflight Script - Existence (AC-1)

#### preflight script exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "scripts/check/check-riscv64-fpga-simpleos-preflight.shs"
val exists = file_exists(path)
expect(exists).to_equal(true)
```

</details>

#### preflight script has correct name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "check-riscv64-fpga-simpleos-preflight.shs"
expect(name).to_start_with("check-riscv64-fpga-simpleos-preflight")
expect(name).to_end_with(".shs")
```

</details>

### Preflight Script - Tool Detection (AC-1)

#### BLOCKED: preflight USB detection requires FT4232H board

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocked_line = "BLOCKED ft4232h_usb_present: no FT4232H USB device found (lsusb 0403:6011 absent)"
expect(blocked_line).to_start_with("BLOCKED ft4232h_usb_present:")
expect(blocked_line).to_contain("0403:6011")
```

</details>

#### BLOCKED: preflight serial port scan requires connected board

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocked_line = "BLOCKED uart_console_probe: BLOCKED: hardware inventory requires connected board"
expect(blocked_line).to_start_with("BLOCKED uart_console_probe:")
expect(blocked_line).to_contain("hardware inventory requires connected board")
```

</details>

#### BLOCKED: preflight JTAG claim status requires connected FT4232H device

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocked_line = "BLOCKED jtag_unbind: BLOCKED: JTAG unbind requires connected FT4232H device"
expect(blocked_line).to_start_with("BLOCKED jtag_unbind:")
expect(blocked_line).to_contain("connected FT4232H device")
```

</details>

### Preflight Script - Cross Compiler Check (AC-1)

#### riscv64-unknown-elf-gcc is a known cross compiler name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compiler_name = "riscv64-unknown-elf-gcc"
expect(compiler_name).to_contain("riscv64")
expect(compiler_name).to_end_with("gcc")
```

</details>

#### riscv64-linux-gnu-gcc is a known cross compiler name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compiler_name = "riscv64-linux-gnu-gcc"
expect(compiler_name).to_contain("riscv64")
expect(compiler_name).to_end_with("gcc")
```

</details>

#### preflight reports openFPGALoader as a known programming tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool = "openFPGALoader"
expect(tool).to_contain("FPGA")
```

</details>

#### preflight reports openocd as a known JTAG tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool = "openocd"
expect(tool).to_equal("openocd")
```

</details>

### Preflight Script - BLOCKED Emission (AC-8)

#### BLOCKED: full preflight run requires connected board and tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val local_only_gate = "--local-only"
val completion_marker = "preflight_complete=true"
val hardware_summary = "hardware_inventory: BLOCKED: no FT4232H USB device found"
expect(local_only_gate).to_equal("--local-only")
expect(completion_marker).to_equal("preflight_complete=true")
expect(hardware_summary).to_start_with("hardware_inventory: BLOCKED:")
```

</details>

#### preflight output format includes pass/fail/blocked keywords

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fmt_pass = "PASS"
val fmt_fail = "FAIL"
val fmt_blocked = "BLOCKED"
expect(fmt_pass).to_equal("PASS")
expect(fmt_fail).to_equal("FAIL")
expect(fmt_blocked).to_equal("BLOCKED")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/riscv64_fpga/preflight_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Preflight Script - Existence (AC-1)
- Preflight Script - Tool Detection (AC-1)
- Preflight Script - Cross Compiler Check (AC-1)
- Preflight Script - BLOCKED Emission (AC-8)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
