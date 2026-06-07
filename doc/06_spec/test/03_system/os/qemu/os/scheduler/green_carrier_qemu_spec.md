# SimpleOS Green Carrier QEMU Live Specification

> This opt-in live spec validates the SimpleOS green-carrier AP lane in QEMU. When `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1` is set, the spec builds the x86_64 guest probe, boots a two-CPU guest, and checks serial output for the real AP 64-bit entry marker plus green-carrier dispatch and preemption PASS markers.

<!-- sdn-diagram:id=green_carrier_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=green_carrier_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

green_carrier_qemu_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=green_carrier_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Green Carrier QEMU Live Specification

This opt-in live spec validates the SimpleOS green-carrier AP lane in QEMU. When `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1` is set, the spec builds the x86_64 guest probe, boots a two-CPU guest, and checks serial output for the real AP 64-bit entry marker plus green-carrier dispatch and preemption PASS markers.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-simpleos-qemu-carrier |
| Category | SimpleOS / QEMU / Concurrency |
| Status | In Progress |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | N/A |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This opt-in live spec validates the SimpleOS green-carrier AP lane in QEMU.
When `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1` is set, the spec builds the
x86_64 guest probe, boots a two-CPU guest, and checks serial output for the
real AP 64-bit entry marker plus green-carrier dispatch and preemption PASS
markers.

The PASS marker means the freestanding fixed-slot carrier path selected CPU1,
sent the remote green-carrier IPI intent, dispatched task `701`, and recorded
one CPU1 green context-switch count. The PREEMPT_PASS marker means the same
guest probe ran the fixed-slot timer preemption helper and requeued the running
green task. This proves AP startup plus scheduler-visible CPU1 green dispatch
and freestanding timer-preemption evidence. Full hardware context-switch
handoff across APs remains tracked separately.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** N/A

## Research

**Research:** doc/01_research/local/multicore_green.md

## Syntax

Run the fast cached/default lane:

```sh
bin/release/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter
```

Run the live QEMU lane:

```sh
SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1 bin/release/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean
```

## Examples

The live serial output must include:

```text
[smp] AP reached 64-bit entry
[green-carrier-qemu] PASS=true
[green-carrier-qemu] PREEMPT_PASS=true
```

## Scenarios

### SimpleOS green carrier live QEMU proof
_Live green-carrier validation, disabled unless SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1._

#### boots two CPUs and dispatches green work onto the AP carrier CPU

1.  print probe debug
   - Expected: serial contains `AP_ONLINE_MARKER`
   - Expected: serial contains `GREEN_PASS_MARKER`
   - Expected: serial contains `GREEN_PREEMPT_MARKER`


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
    val output_path = "build/os/simpleos_green_carrier_probe.elf"
    val built = _build_probe(output_path, "cranelift") or _build_probe(output_path, "llvm")
    expect(built).to_equal(true)
    val result = _run_probe(output_path)
    val serial = result[0]
    if not _has_required_markers(serial):
        _print_probe_debug(serial, result[1])
    expect(serial.contains(AP_ONLINE_MARKER)).to_equal(true)
    expect(serial.contains(GREEN_PASS_MARKER)).to_equal(true)
    expect(serial.contains(GREEN_PREEMPT_MARKER)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
