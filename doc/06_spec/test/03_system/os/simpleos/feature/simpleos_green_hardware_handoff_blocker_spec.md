# SimpleOS Green Hardware Handoff Blocker Contract

> This SSpec keeps the final SimpleOS green-thread hardware handoff boundary executable. Current QEMU evidence proves AP startup, fixed-slot dispatch, preemption, and scheduler-owned handoff through `SCHED_HANDOFF_PASS=true`, but it must not be treated as final ring/user hardware context-switch proof.

<!-- sdn-diagram:id=simpleos_green_hardware_handoff_blocker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_green_hardware_handoff_blocker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_green_hardware_handoff_blocker_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_green_hardware_handoff_blocker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Green Hardware Handoff Blocker Contract

This SSpec keeps the final SimpleOS green-thread hardware handoff boundary executable. Current QEMU evidence proves AP startup, fixed-slot dispatch, preemption, and scheduler-owned handoff through `SCHED_HANDOFF_PASS=true`, but it must not be treated as final ring/user hardware context-switch proof.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-simpleos-hardware-handoff |
| Category | SimpleOS / Concurrency |
| Status | Blocked |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/03_system/os/simpleos/feature/simpleos_green_hardware_handoff_blocker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec keeps the final SimpleOS green-thread hardware handoff boundary
executable. Current QEMU evidence proves AP startup, fixed-slot dispatch,
preemption, and scheduler-owned handoff through `SCHED_HANDOFF_PASS=true`, but
it must not be treated as final ring/user hardware context-switch proof.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/01_research/local/multicore_green.md

## Scenarios

### SimpleOS green hardware handoff blocker

#### keeps scheduler handoff evidence separate from final hardware handoff evidence

- Read the blocker and current QEMU green-carrier spec
- Verify the existing scheduler marker remains documented as non-final evidence
- Verify the current guest probe does not claim the future final marker
   - Expected: absent_in_text(probe, "HW_HANDOFF_PASS=true") equals `1`
   - Expected: absent_in_text(probe, "USER_ENTRY_PASS=true") equals `1`
   - Expected: absent_in_text(probe, "USER_SYSCALL_PASS=true") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the blocker and current QEMU green-carrier spec")
val blocker = read_text("doc/08_tracking/bug/simpleos_green_hardware_context_switch_handoff_2026-06-07.md")
val qemu_spec = read_text("test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl")
val probe = read_text("examples/09_embedded/simple_os/arch/x86_64/green_carrier_probe_entry.spl")

step("Verify the existing scheduler marker remains documented as non-final evidence")
expect(blocker).to_contain("SCHED_HANDOFF_PASS=true")
expect(blocker).to_contain("HW_HANDOFF_PASS=true")
expect(blocker).to_contain("do not overload")
expect(qemu_spec).to_contain("GREEN_SCHED_HANDOFF_MARKER")
expect(qemu_spec).to_contain("GREEN_HW_HANDOFF_MARKER")
expect(qemu_spec).to_contain("GREEN_USER_ENTRY_MARKER")
expect(qemu_spec).to_contain("GREEN_USER_SYSCALL_MARKER")
expect(qemu_spec).to_contain("SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE")

step("Verify the current guest probe does not claim the future final marker")
expect(absent_in_text(probe, "HW_HANDOFF_PASS=true")).to_equal(1)
expect(absent_in_text(probe, "USER_ENTRY_PASS=true")).to_equal(1)
expect(absent_in_text(probe, "USER_SYSCALL_PASS=true")).to_equal(1)
```

</details>

#### names the concrete context switch and user-entry proof points

- Read blocker and handoff implementation surfaces
- Verify the blocker links the live probe and current context-switch symbols
- Verify current implementation files expose the named proof points


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read blocker and handoff implementation surfaces")
val blocker = read_text("doc/08_tracking/bug/simpleos_green_hardware_context_switch_handoff_2026-06-07.md")
val context_switch = read_text("src/os/kernel/scheduler/context_switch.spl")
val x86_context = read_text("src/os/kernel/arch/x86_64/context.spl")
val user_entry = read_text("src/os/kernel/arch/x86_64/user_entry.spl")
val syscall_entry = read_text("src/os/kernel/arch/x86_64/cpu.spl")
val syscall_dispatch = read_text("src/os/kernel/ipc/syscall.spl")
val probe = read_text("examples/09_embedded/simple_os/arch/x86_64/green_carrier_probe_entry.spl")

step("Verify the blocker links the live probe and current context-switch symbols")
expect(blocker).to_contain("src/os/kernel/scheduler/context_switch.spl")
expect(blocker).to_contain("src/os/kernel/arch/x86_64/context.spl")
expect(blocker).to_contain("src/os/kernel/arch/x86_64/user_entry.spl")
expect(blocker).to_contain("src/os/kernel/arch/x86_64/cpu.spl")
expect(blocker).to_contain("src/os/kernel/ipc/syscall.spl")
expect(blocker).to_contain("green_carrier_probe_entry.spl")
expect(blocker).to_contain("USER_ENTRY_PASS=true")
expect(blocker).to_contain("USER_SYSCALL_PASS=true")

step("Verify current implementation files expose the named proof points")
expect(context_switch).to_contain("context_restore")
expect(context_switch).to_contain("switch_context_with_as")
expect(x86_context).to_contain("arch_x86_64_enter_user_task")
expect(x86_context).to_contain("rt_x86_enter_user_first")
expect(user_entry).to_contain("dispatch_enter_user_blocking")
expect(syscall_entry).to_contain("kernel_syscall_entry_asm")
expect(syscall_entry).to_contain("rt_syscall_dispatch")
expect(syscall_dispatch).to_contain("syscall_handler")
expect(probe).to_contain("SCHED_HANDOFF_PASS")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/multicore_green.md](doc/02_requirements/feature/multicore_green.md)
- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Design:** [doc/05_design/multicore_green.md](doc/05_design/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
