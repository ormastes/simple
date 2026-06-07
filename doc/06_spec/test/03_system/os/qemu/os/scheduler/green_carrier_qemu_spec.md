# SimpleOS Green Carrier QEMU Live Specification

> This opt-in live spec validates the SimpleOS green-carrier AP lane in QEMU. When `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1` is set, the spec builds the x86_64 guest probe, boots a two-CPU guest, and checks serial output for the real AP 64-bit entry marker plus fixed green-carrier dispatch, preemption, and scheduler-owned handoff PASS markers.

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

This opt-in live spec validates the SimpleOS green-carrier AP lane in QEMU. When `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1` is set, the spec builds the x86_64 guest probe, boots a two-CPU guest, and checks serial output for the real AP 64-bit entry marker plus fixed green-carrier dispatch, preemption, and scheduler-owned handoff PASS markers.

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
real AP 64-bit entry marker plus fixed green-carrier dispatch, preemption, and
scheduler-owned handoff PASS markers.

The PASS marker means the freestanding fixed-slot carrier helper selected CPU1,
sent the remote green-carrier IPI intent, dispatched task `701`, and recorded
one CPU1 green context-switch count. The PREEMPT_PASS marker means the same
guest probe ran the fixed-slot timer preemption helper and requeued the running
green task. The SCHED_HANDOFF_PASS marker means the real `Scheduler` accepted
the green-carrier dispatch through `run_green_carrier_once`, recorded task
`701` and one green context switch on CPU1, and left the normal OS task slot
unchanged. Together these markers prove AP startup plus live guest evidence for
both the freestanding helper path and the scheduler-owned green handoff path.

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
[green-carrier-qemu] SCHED_HANDOFF_PASS=true
```

## Scenarios

### SimpleOS green carrier live QEMU proof
_Live green-carrier validation, disabled unless SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1._

#### boots two CPUs and dispatches green work through the scheduler-owned AP carrier

1. Skip the live QEMU lane unless SIMPLEOS_GREEN_CARRIER_QEMU_LIVE is enabled
   - Expected: _enabled() is false
2. Skip live QEMU execution on hosts without qemu-system-x86_64
   - Expected: _qemu_available() is false
3. Build the SimpleOS green carrier guest probe
   - Expected: built is true
4. Boot the two-CPU guest probe under QEMU
5.  print probe debug
6. Verify AP startup and all green carrier proof markers
   - Expected: serial contains `AP_ONLINE_MARKER`
   - Expected: serial contains `GREEN_PASS_MARKER`
   - Expected: serial contains `GREEN_PREEMPT_MARKER`
   - Expected: serial contains `GREEN_SCHED_HANDOFF_MARKER`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _enabled():
    step("Skip the live QEMU lane unless SIMPLEOS_GREEN_CARRIER_QEMU_LIVE is enabled")
    expect(_enabled()).to_equal(false)
elif not _qemu_available():
    step("Skip live QEMU execution on hosts without qemu-system-x86_64")
    expect(_qemu_available()).to_equal(false)
else:
    step("Build the SimpleOS green carrier guest probe")
    val output_path = "build/os/simpleos_green_carrier_probe.elf"
    val built = _build_probe(output_path, "cranelift") or _build_probe(output_path, "llvm")
    expect(built).to_equal(true)
    step("Boot the two-CPU guest probe under QEMU")
    val result = _run_probe(output_path)
    val serial = result[0]
    if not _has_required_markers(serial):
        _print_probe_debug(serial, result[1])
    step("Verify AP startup and all green carrier proof markers")
    expect(serial.contains(AP_ONLINE_MARKER)).to_equal(true)
    expect(serial.contains(GREEN_PASS_MARKER)).to_equal(true)
    expect(serial.contains(GREEN_PREEMPT_MARKER)).to_equal(true)
    expect(serial.contains(GREEN_SCHED_HANDOFF_MARKER)).to_equal(true)
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
