# Qemu Boot Specification

> <details>

<!-- sdn-diagram:id=qemu_boot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=qemu_boot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

qemu_boot_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=qemu_boot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qemu Boot Specification

## Scenarios

### QEMU debug boot runner portable smoke

#### records debug info unavailable formatting

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text_output = "Debug information not available"
expect(text_output).to_contain("Debug")
```

</details>

#### records stack frame fields without reserved names

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbol_name = "kernel_main"
val file_name = "kernel.spl"
expect(symbol_name).to_equal("kernel_main")
expect(file_name).to_end_with(".spl")
```

</details>

#### parses representative hex values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_hex_smoke("0x1234")).to_equal(0x1234)
expect(parse_hex_smoke("ff")).to_equal(255)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/t32_tools/qemu_boot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- QEMU debug boot runner portable smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
