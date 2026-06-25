# Simpleos Smp Ap Live Specification

> _Live FR-SOS-017 validation, disabled unless SIMPLEOS_QEMU_SMP_AP_LIVE=1._

<!-- sdn-diagram:id=simpleos_smp_ap_live_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_smp_ap_live_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_smp_ap_live_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_smp_ap_live_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Smp Ap Live Specification

## Scenarios

### SimpleOS x86 SMP AP live QEMU proof
_Live FR-SOS-017 validation, disabled unless SIMPLEOS_QEMU_SMP_AP_LIVE=1._

#### boots with two CPUs and observes an AP reaching the 64-bit online hook

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _enabled():
    expect(_enabled()).to_equal(false)
elif not _qemu_available():
    expect(_qemu_available()).to_equal(false)
else:
    val output_path = "build/os/simpleos_smp_ap_probe_32.elf"
    val built = _build_smp_probe(output_path) or _build_smp_probe_with_llvm(output_path)
    expect(built).to_equal(true)
    val result = _run_smp_probe(output_path)
    val serial = result[0]
    if not serial.contains(AP_ONLINE_MARKER):
        val saw_boot = serial.contains("[smp-probe] boot")
        val saw_registered = serial.contains("[smp-probe] registered")
        val saw_startup_sent = serial.contains("[smp-probe] startup sent")
        print "[simpleos_smp_ap_live_spec] qemu exit={result[1]}"
        print "[simpleos_smp_ap_live_spec] saw boot={saw_boot}"
        print "[simpleos_smp_ap_live_spec] saw registered={saw_registered}"
        print "[simpleos_smp_ap_live_spec] saw startup-sent={saw_startup_sent}"
        print "[simpleos_smp_ap_live_spec] saw ap-marker=false"
    expect(serial.contains(AP_ONLINE_MARKER)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_smp_ap_live_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS x86 SMP AP live QEMU proof

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
