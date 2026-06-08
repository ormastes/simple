# SimpleOS Green Hardware Handoff Blocker Contract

> This SSpec keeps the final SimpleOS green-thread hardware handoff boundary executable. Current QEMU evidence proves AP startup, fixed-slot dispatch, preemption, and scheduler-owned handoff through `SCHED_HANDOFF_PASS=true`, but it must not be treated as final ring/user hardware context-switch proof. `USER_HANDOFF_READY=true` is also non-final evidence: it proves real scheduler user-task construction and non-entering syscall-14 validation in the guest, not the AP ring/user transition. `USER_ENTRY_BRIDGE_READY=true` is non-final bridge readiness evidence: it proves the live guest has the x86_64 trap runtime, SYSCALL entry install, and linked entry trampoline ready before an actual ring/user run. `USER_SYSCALL_BRIDGE_READY=true` is non-final syscall bridge readiness evidence: it proves the strong syscall shim path can dispatch debug_write before a user-mode payload issues a syscall.

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

# SimpleOS Green Hardware Handoff Blocker Contract

This SSpec keeps the final SimpleOS green-thread hardware handoff boundary executable. Current QEMU evidence proves AP startup, fixed-slot dispatch, preemption, and scheduler-owned handoff through `SCHED_HANDOFF_PASS=true`, but it must not be treated as final ring/user hardware context-switch proof. `USER_HANDOFF_READY=true` is also non-final evidence: it proves real scheduler user-task construction and non-entering syscall-14 validation in the guest, not the AP ring/user transition. `USER_ENTRY_BRIDGE_READY=true` is non-final bridge readiness evidence: it proves the live guest has the x86_64 trap runtime, SYSCALL entry install, and linked entry trampoline ready before an actual ring/user run. `USER_SYSCALL_BRIDGE_READY=true` is non-final syscall bridge readiness evidence: it proves the strong syscall shim path can dispatch debug_write before a user-mode payload issues a syscall.

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
`USER_HANDOFF_READY=true` is also non-final evidence: it proves real scheduler
user-task construction and non-entering syscall-14 validation in the guest, not
the AP ring/user transition. `USER_ENTRY_BRIDGE_READY=true` is non-final bridge
readiness evidence: it proves the live guest has the x86_64 trap runtime,
SYSCALL entry install, and linked entry trampoline ready before an actual
ring/user run. `USER_SYSCALL_BRIDGE_READY=true` is non-final syscall bridge
readiness evidence: it proves the strong syscall shim path can dispatch
debug_write before a user-mode payload issues a syscall.

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

- `SCHED_HANDOFF_PASS=true` is scheduler-owned evidence only.
- `USER_HANDOFF_READY=true` is scheduler/user handoff readiness evidence only.
- `USER_ENTRY_BRIDGE_READY=true` is syscall/user-entry bridge readiness evidence only.
- `USER_SYSCALL_BRIDGE_READY=true` is syscall-shim bridge readiness evidence only.
- Final hardware evidence requires `HW_HANDOFF_PASS=true`.
- Final user-entry evidence requires `USER_ENTRY_PASS=true`.
- Final syscall-return evidence requires `USER_SYSCALL_PASS=true`.

## TUI Capture

```text
Simple Test Runner v1.0.0-beta
Running: test/03_system/os/simpleos/feature/simpleos_green_hardware_handoff_blocker_spec.spl
[1/1] test/03_system/os/simpleos/feature/simpleos_green_hardware_handoff_blocker_spec.spl PASSED
Files: 1
Passed: 3
Failed: 0
```

## Traceability Expectations

- The blocker document must keep `SCHED_HANDOFF_PASS=true` visible as current
  scheduler-owned evidence.
- The blocker document must keep `HW_HANDOFF_PASS=true` visible as future final
  hardware evidence.
- The blocker document must keep `USER_ENTRY_PASS=true` visible as future final
  user-entry evidence.
- The blocker document must keep `USER_SYSCALL_PASS=true` visible as future
  syscall-return evidence.
- The QEMU spec must expose separate constants for scheduler handoff, hardware
  handoff, user entry, and user syscall markers.
- The QEMU spec must expose a separate non-final user handoff readiness marker.
- The QEMU spec must expose a separate non-final user-entry bridge readiness marker.
- The QEMU spec must expose a separate non-final user-syscall bridge readiness marker.
- The QEMU spec must keep `SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1` as an
  opt-in gate.
- The current guest probe must not print the final hardware/user marker triplet.
- The blocker must name the current context-switch proof-point files so the
  future implementation lane can find the bridge instead of inventing another
  probe.
- The blocker must name `context_restore` and `switch_context_with_as`.
- The blocker must name `arch_x86_64_enter_user_task` and
  `rt_x86_enter_user_first`.
- The blocker must name `dispatch_enter_user_blocking`.
- The blocker must name `kernel_syscall_entry_asm` and `rt_syscall_dispatch`.
- The blocker must name `syscall_handler`.
- The feature requirements must keep `REQ-MCG-007` tied to the final marker
  triplet.
- The NFR requirements must keep `NFR-MCG-012` tied to the opt-in live gate.
- The SimpleOS evidence report must not claim final ring/user hardware handoff.
- The SimpleOS evidence report must show the current blocker contract has three
  scenarios.
- The current blocker contract can pass while the final hardware handoff remains
  blocked, because passing this SSpec proves honesty of the boundary rather than
  completion of the boundary.
- The final live gate can close only when the guest emits all final markers from
  the real AP ring/user path.

## Verification Expectations

- Run this SSpec after changing the blocker, QEMU spec, requirements, or
  SimpleOS evidence report.
- Regenerate
  `doc/06_spec/test/03_system/os/simpleos/feature/simpleos_green_hardware_handoff_blocker_spec.md`
  after changing this SSpec.
- Keep historical evidence in the report when useful, but keep the summary row
  and newest refresh entry aligned with the current scenario count.
- Do not remove the opt-in final live gate while the final marker triplet is
  absent from the guest probe.
- Do not mark the multicore-green feature `done` while
  `doc/08_tracking/bug/simpleos_green_hardware_context_switch_handoff_2026-06-07.md`
  is open.

## Scenarios

### SimpleOS green hardware handoff blocker

#### keeps scheduler handoff evidence separate from final hardware handoff evidence

- Read the blocker and current QEMU green-carrier spec
- Verify the existing scheduler markers remain documented as non-final evidence
- Verify the current guest probe does not claim the future final marker
   - Expected: absent_in_text(probe, "HW_HANDOFF_PASS=true") equals `1`
   - Expected: absent_in_text(probe, "USER_ENTRY_PASS=true") equals `1`
   - Expected: absent_in_text(probe, "USER_SYSCALL_PASS=true") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the blocker and current QEMU green-carrier spec")
val blocker = read_text("doc/08_tracking/bug/simpleos_green_hardware_context_switch_handoff_2026-06-07.md")
val qemu_spec = read_text("test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl")
val probe = read_text("examples/09_embedded/simple_os/arch/x86_64/green_carrier_probe_entry.spl")

step("Verify the existing scheduler markers remain documented as non-final evidence")
expect(blocker).to_contain("SCHED_HANDOFF_PASS=true")
expect(blocker).to_contain("USER_HANDOFF_READY=true")
expect(blocker).to_contain("USER_ENTRY_BRIDGE_READY=true")
expect(blocker).to_contain("USER_SYSCALL_BRIDGE_READY=true")
expect(blocker).to_contain("HW_HANDOFF_PASS=true")
expect(blocker).to_contain("do not overload")
expect(qemu_spec).to_contain("GREEN_SCHED_HANDOFF_MARKER")
expect(qemu_spec).to_contain("GREEN_USER_HANDOFF_READY_MARKER")
expect(qemu_spec).to_contain("GREEN_USER_ENTRY_BRIDGE_READY_MARKER")
expect(qemu_spec).to_contain("GREEN_USER_SYSCALL_BRIDGE_READY_MARKER")
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

Runnable source: 40 lines folded for reproduction.
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
```

</details>

#### keeps requirements and evidence report aligned with the final live gate

- Read requirements, NFR, QEMU spec, and current evidence report
- Verify requirement docs require the final marker triplet
- Verify the QEMU spec owns the explicit final live gate
- Verify the evidence report does not claim final ring/user handoff


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
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

step("Verify the evidence report does not claim final ring/user handoff")
expect(report).to_contain("| SimpleOS final hardware handoff blocker contract | PASS | 3 |")
expect(report).to_contain("final hardware handoff blocker contract: 3 scenarios")
expect(report).to_contain("does not claim final")
expect(report).to_contain("final live hardware handoff lane remains opt-in and unclaimed")
expect(report).to_contain("SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1")
expect(report).to_contain("A scheduler-only")
expect(report).to_contain("must not print any of those final markers")
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
