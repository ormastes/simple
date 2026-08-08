# Simpleos Reboot Live Specification

> _Live reset validation, disabled unless SIMPLEOS_QEMU_REBOOT_LIVE=1._

<!-- sdn-diagram:id=simpleos_reboot_live_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_reboot_live_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_reboot_live_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_reboot_live_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Reboot Live Specification

## Scenarios

### SimpleOS x86 reboot reset live QEMU probe
_Live reset validation, disabled unless SIMPLEOS_QEMU_REBOOT_LIVE=1._

#### boots a probe that requests reset through the x86 reset-control port

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _enabled():
    expect(_enabled()).to_equal(false)
elif not _qemu_available():
    expect(_qemu_available()).to_equal(false)
else:
    val output_path = "build/os/simpleos_reboot_probe_32.elf"
    expect(_build_probe(output_path)).to_equal(true)
    val result = _run_probe(output_path)
    val serial = result[0]
    val exit_code = result[1]
    expect(serial.contains("[reboot-probe] before reset")).to_equal(true)
    if exit_code == 0:
        expect(exit_code).to_equal(0)
    else:
        expect(exit_code).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_reboot_live_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS x86 reboot reset live QEMU probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
