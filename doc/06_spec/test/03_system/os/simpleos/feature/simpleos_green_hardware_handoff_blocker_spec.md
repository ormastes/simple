# SimpleOS Green Hardware Handoff Closure Contract

> This SSpec keeps the final SimpleOS green-thread hardware handoff closure executable. Earlier QEMU evidence proved AP startup, fixed-slot dispatch, preemption, scheduler-owned handoff through `SCHED_HANDOFF_PASS=true`, and prerequisite user-entry readiness markers. The closed final live lane now also requires `HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, and `USER_SYSCALL_PASS=true` from the real AP ring/user path so prerequisite markers cannot be mistaken for final hardware proof.

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
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Green Hardware Handoff Closure Contract

This SSpec keeps the final SimpleOS green-thread hardware handoff closure executable. Earlier QEMU evidence proved AP startup, fixed-slot dispatch, preemption, scheduler-owned handoff through `SCHED_HANDOFF_PASS=true`, and prerequisite user-entry readiness markers. The closed final live lane now also requires `HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, and `USER_SYSCALL_PASS=true` from the real AP ring/user path so prerequisite markers cannot be mistaken for final hardware proof.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-simpleos-hardware-handoff |
| Category | SimpleOS / Concurrency |
| Status | Closed |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/03_system/os/simpleos/feature/simpleos_green_hardware_handoff_blocker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec keeps the final SimpleOS green-thread hardware handoff closure
executable. Earlier QEMU evidence proved AP startup, fixed-slot dispatch,
preemption, scheduler-owned handoff through `SCHED_HANDOFF_PASS=true`, and
prerequisite user-entry readiness markers. The closed final live lane now also
requires `HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, and
`USER_SYSCALL_PASS=true` from the real AP ring/user path so prerequisite
markers cannot be mistaken for final hardware proof.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/01_research/local/multicore_green.md

## Syntax

Run the blocker contract:

```sh
./src/compiler_rust/target/debug/simple test test/03_system/os/simpleos/feature/simpleos_green_hardware_handoff_blocker_spec.spl --mode=interpreter --clean
```

The final live QEMU lane is separate and opt-in:

```sh
SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1 bin/release/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean
```

## Examples

- `SCHED_HANDOFF_PASS=true` is scheduler-owned prerequisite evidence.
- `USER_HANDOFF_READY=true` is scheduler/user handoff readiness evidence.
- `USER_ENTRY_BRIDGE_READY=true` is syscall/user-entry bridge readiness evidence.
- `USER_SYSCALL_BRIDGE_READY=true` is syscall-shim bridge readiness evidence.
- `USER_CR3_READY=true` is final-path CR3 readiness evidence.
- Closed final hardware evidence requires `HW_HANDOFF_PASS=true`.
- Closed final user-entry evidence requires `USER_ENTRY_PASS=true`.
- Closed final syscall-return evidence requires `USER_SYSCALL_PASS=true`.

## TUI Capture

```text
Simple Test Runner v1.0.0-beta
Running: test/03_system/os/simpleos/feature/simpleos_green_hardware_handoff_blocker_spec.spl
Spec file completed: simpleos_green_hardware_handoff_blocker_spec.spl PASSED
Files: 1
Passed: 3
Failed: 0
```

## Traceability Expectations

- The closure document must keep `SCHED_HANDOFF_PASS=true` visible as
  scheduler-owned prerequisite evidence.
- The closure document must keep `HW_HANDOFF_PASS=true` visible as closed final
  hardware evidence.
- The closure document must keep `USER_ENTRY_PASS=true` visible as closed final
  user-entry evidence.
- The closure document must keep `USER_SYSCALL_PASS=true` visible as closed
  syscall-return evidence.
- The QEMU spec must expose separate constants for scheduler handoff, hardware
  handoff, user entry, and user syscall markers.
- The QEMU spec must expose a separate non-final user handoff readiness marker.
- The QEMU spec must expose a separate non-final user-entry bridge readiness marker.
- The QEMU spec must expose a separate non-final user-syscall bridge readiness marker.
- The QEMU spec must expose a separate non-final final-path CR3 readiness marker.
- The QEMU spec must keep `SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1` as an
  opt-in gate.
- The final live gate must print the final hardware/user marker triplet.
- The closure document must name the current context-switch proof-point files.
- The closure document must name `context_restore` and `switch_context_with_as`.
- The closure document must name `arch_x86_64_enter_user_task` and
  `rt_x86_enter_user_first`.
- The closure document must name `dispatch_enter_user_blocking`.
- The closure document must name `kernel_syscall_entry_asm` and `rt_syscall_dispatch`.
- The closure document must name `syscall_handler`.
- The feature requirements must keep `REQ-MCG-007` tied to the final marker
  triplet.
- The NFR requirements must keep `NFR-MCG-012` tied to the opt-in live gate.
- The SimpleOS evidence report must claim final ring/user hardware handoff only
  through the opt-in live gate and final marker triplet.
- The SimpleOS evidence report must show the current blocker contract has three
  scenarios.
- The closure contract can pass only while the final live gate evidence remains
  documented as closed by the real AP ring/user path.
- The closure document must record the direct final-entry probe finding: legacy `cr3=1`
  is insufficient, and the current minimal probe still needs a safe
  PMM/VMM bootstrap or minimal user page-table allocator before final markers
  could be claimed.

## Verification Expectations

- Run this SSpec after changing the blocker, QEMU spec, requirements, or
  SimpleOS evidence report.
- Regenerate
  `doc/06_spec/test/03_system/os/simpleos/feature/simpleos_green_hardware_handoff_blocker_spec.md`
  after changing this SSpec.
- Keep historical evidence in the report when useful, but keep the summary row
  and newest refresh entry aligned with the current scenario count.
- Do not remove the opt-in final live gate.
- Do not mark the multicore-green feature `done` solely because the SimpleOS
  final handoff is closed; the broader Go-like roadmap must still pass release
  verification.

## Scenarios

### SimpleOS green hardware handoff closure

#### keeps prerequisite evidence separate from final handoff closure evidence

- Read the blocker and current QEMU green-carrier spec
- Verify the prerequisite and final markers remain documented separately
- Verify the guest probe keeps final payload emission behind real final entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the blocker and current QEMU green-carrier spec")
val blocker = read_text("doc/08_tracking/bug/simpleos_green_hardware_context_switch_handoff_2026-06-07.md")
val qemu_spec = read_text("test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl")
val probe = read_text("examples/09_embedded/simple_os/arch/x86_64/green_carrier_probe_entry.spl")

step("Verify the prerequisite and final markers remain documented separately")
expect(blocker).to_contain("Status: CLOSED")
expect(blocker).to_contain("SCHED_HANDOFF_PASS=true")
expect(blocker).to_contain("USER_HANDOFF_READY=true")
expect(blocker).to_contain("USER_ENTRY_BRIDGE_READY=true")
expect(blocker).to_contain("USER_SYSCALL_BRIDGE_READY=true")
expect(blocker).to_contain("USER_CR3_READY=true")
expect(blocker).to_contain("HW_HANDOFF_PASS=true")
expect(blocker).to_contain("USER_ENTRY_PASS=true")
expect(blocker).to_contain("USER_SYSCALL_PASS=true")
expect(blocker).to_contain("This blocker no longer prevents")
expect(blocker).to_contain("do not overload")
expect(qemu_spec).to_contain("GREEN_SCHED_HANDOFF_MARKER")
expect(qemu_spec).to_contain("GREEN_USER_HANDOFF_READY_MARKER")
expect(qemu_spec).to_contain("GREEN_USER_ENTRY_BRIDGE_READY_MARKER")
expect(qemu_spec).to_contain("GREEN_USER_SYSCALL_BRIDGE_READY_MARKER")
expect(qemu_spec).to_contain("GREEN_USER_CR3_READY_MARKER")
expect(qemu_spec).to_contain("GREEN_HW_HANDOFF_MARKER")
expect(qemu_spec).to_contain("GREEN_USER_ENTRY_MARKER")
expect(qemu_spec).to_contain("GREEN_USER_SYSCALL_MARKER")
expect(qemu_spec).to_contain("SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE")

step("Verify the guest probe keeps final payload emission behind real final entry")
expect(probe).to_contain("_make_final_marker_payload")
expect(probe).to_contain("_run_final_ring_user_handoff_probe")
expect(probe).to_contain("USER_CR3_READY")
expect(probe).to_contain("dispatch_enter_user_blocking")
expect(qemu_spec).to_contain("expect(serial).to_contain(GREEN_HW_HANDOFF_MARKER)")
expect(qemu_spec).to_contain("expect(serial).to_contain(GREEN_USER_ENTRY_MARKER)")
expect(qemu_spec).to_contain("expect(serial).to_contain(GREEN_USER_SYSCALL_MARKER)")
```

</details>

#### names the concrete context switch and user-entry proof points

- Read blocker and handoff implementation surfaces
- Verify the blocker links the live probe and current context-switch symbols
- Verify current implementation files expose the named proof points


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read blocker and handoff implementation surfaces")
val blocker = read_text("doc/08_tracking/bug/simpleos_green_hardware_context_switch_handoff_2026-06-07.md")
val context_switch = read_text("src/os/kernel/scheduler/context_switch.spl")
val x86_context = read_text("src/os/kernel/arch/x86_64/context.spl")
val user_entry = read_text("src/os/kernel/arch/x86_64/user_entry.spl")
val user_entry_validation = read_text("src/os/kernel/arch/x86_64/user_entry_validation.spl")
val syscall_entry = read_text("src/os/kernel/arch/x86_64/cpu.spl")
val syscall_dispatch = read_text("src/os/kernel/ipc/syscall.spl")
val probe = read_text("examples/09_embedded/simple_os/arch/x86_64/green_carrier_probe_entry.spl")

step("Verify the blocker links the live probe and current context-switch symbols")
expect(blocker).to_contain("src/os/kernel/scheduler/context_switch.spl")
expect(blocker).to_contain("src/os/kernel/arch/x86_64/context.spl")
expect(blocker).to_contain("src/os/kernel/arch/x86_64/user_entry.spl")
expect(blocker).to_contain("src/os/kernel/arch/x86_64/user_entry_validation.spl")
expect(blocker).to_contain("src/os/kernel/arch/x86_64/cpu.spl")
expect(blocker).to_contain("src/os/kernel/ipc/syscall.spl")
expect(blocker).to_contain("green_carrier_probe_entry.spl")
expect(blocker).to_contain("USER_ENTRY_PASS=true")
expect(blocker).to_contain("USER_SYSCALL_PASS=true")
expect(blocker).to_contain("Hosted Real-Spawn Handoff Prerequisite Fix")
expect(blocker).to_contain("create_user_task_pid")
expect(blocker).to_contain("validation-ready TCB")
expect(blocker).to_contain("This closes the hosted real-spawn prerequisite")
expect(blocker).to_contain("Guest User Handoff Readiness Prerequisite")
expect(blocker).to_contain("Direct Final-Entry Probe Finding")
expect(blocker).to_contain("legacy `cr3=1`")
expect(blocker).to_contain("safe direct-boot memory bootstrap")
expect(blocker).to_contain("user page-table allocator")

step("Verify current implementation files expose the named proof points")
expect(context_switch).to_contain("context_restore")
expect(context_switch).to_contain("switch_context_with_as")
expect(x86_context).to_contain("arch_x86_64_enter_user_task")
expect(x86_context).to_contain("rt_x86_enter_user_first")
expect(user_entry).to_contain("dispatch_enter_user_blocking")
expect(user_entry_validation).to_contain("validate_enter_user_blocking_handoff")
expect(syscall_entry).to_contain("kernel_syscall_entry_asm")
expect(syscall_entry).to_contain("rt_syscall_dispatch")
expect(syscall_dispatch).to_contain("syscall_handler")
expect(probe).to_contain("SCHED_HANDOFF_PASS")
expect(probe).to_contain("USER_HANDOFF_READY")
expect(probe).to_contain("USER_ENTRY_BRIDGE_READY")
expect(probe).to_contain("USER_SYSCALL_BRIDGE_READY")
expect(probe).to_contain("USER_CR3_READY")
```

</details>

#### keeps requirements and evidence report aligned with the final live gate

- Read requirements, NFR, QEMU spec, and current evidence report
- Verify requirement docs require the final marker triplet
- Verify the QEMU spec owns the explicit final live gate
- Verify the evidence report claims final ring/user handoff through live markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read requirements, NFR, QEMU spec, and current evidence report")
val feature_req = read_text("doc/02_requirements/feature/multicore_green.md")
val nfr_req = read_text("doc/02_requirements/nfr/multicore_green.md")
val qemu_spec = read_text("test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl")
val report = read_text("doc/09_report/simpleos_multicore_green_evidence_2026-06-07.md")

step("Verify requirement docs require the final marker triplet")
expect(feature_req).to_contain("REQ-MCG-007")
expect(feature_req).to_contain("HW_HANDOFF_PASS=true")
expect(feature_req).to_contain("USER_ENTRY_PASS=true")
expect(feature_req).to_contain("USER_SYSCALL_PASS=true")
expect(nfr_req).to_contain("NFR-MCG-012")
expect(nfr_req).to_contain("SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1")

step("Verify the QEMU spec owns the explicit final live gate")
expect(qemu_spec).to_contain("_hw_handoff_enabled")
expect(qemu_spec).to_contain("GREEN_HW_HANDOFF_MARKER")
expect(qemu_spec).to_contain("GREEN_USER_ENTRY_MARKER")
expect(qemu_spec).to_contain("GREEN_USER_SYSCALL_MARKER")

step("Verify the evidence report claims final ring/user handoff through live markers")
expect(report).to_contain("| SimpleOS final hardware handoff blocker contract | PASS | 3 |")
expect(report).to_contain("final hardware handoff blocker contract: 3 scenarios")
expect(report).to_contain("Final Ring/User Handoff PASS")
expect(report).to_contain("final live green-carrier QEMU lane now proves the real AP ring/user path")
expect(report).to_contain("SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1")
expect(report).to_contain("[green-carrier-qemu] HW_HANDOFF_PASS=true")
expect(report).to_contain("[green-carrier-qemu] USER_ENTRY_PASS=true")
expect(report).to_contain("[green-carrier-qemu] USER_SYSCALL_PASS=true")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/multicore_green.md](doc/02_requirements/feature/multicore_green.md)
- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Design:** [doc/05_design/multicore_green.md](doc/05_design/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
