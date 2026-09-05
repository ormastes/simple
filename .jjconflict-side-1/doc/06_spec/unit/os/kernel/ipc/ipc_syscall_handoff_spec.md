# Ipc Syscall Handoff Specification

> Tests covering IPC syscall handoff.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ipc Syscall Handoff Specification

## Scenarios

### IPC syscall handoff

#### blocking recv records the current task as a port waiter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- blocking recv records the current task as a port waiter
   - Expected: state.result.value equals `0`
   - Expected: has_waiter is true
   - Expected: task_id.id equals `receiver.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocking recv records the current task as a port waiter")
var scheduler = Scheduler.new()
var ipc = IpcManager.new()
val receiver = scheduler.get_current()
val port = ipc.create_port(receiver, "ipc_blocking_recv")

val state = _handle_ipc_recv_state(
    SyscallArgs(
        id: 21,
        arg0: port.id,
        arg1: 1,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    ipc
)

expect(state.result.value).to_equal(0)
val waiter = state.ipc.get_first_waiter(port.id)
val has_waiter = waiter != nil
expect(has_waiter).to_equal(true)
if waiter != nil:
    val task_id = waiter
    expect(task_id.id).to_equal(receiver.id)
```

</details>

#### send unblocks the first waiting receiver and consumes one waiter

- send unblocks the first waiting receiver and consumes one waiter
   - Expected: state.result.value equals `0`
   - Expected: state.ipc.get_first_waiter(port.id) equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("send unblocks the first waiting receiver and consumes one waiter")
var scheduler = Scheduler.new()
var ipc = IpcManager.new()
val receiver = TaskId(id: 99)
val port = ipc.create_port(receiver, "ipc_send_wake")
ipc.add_waiter(port, receiver)

val state = _handle_ipc_send_state(
    SyscallArgs(
        id: 20,
        arg0: port.id,
        arg1: 7,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    ipc
)

expect(state.result.value).to_equal(0)
expect(state.ipc.get_first_waiter(port.id)).to_equal(nil)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/ipc/ipc_syscall_handoff_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering IPC syscall handoff.
- IPC syscall handoff

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `050c649231a7efd609004f4471c68727af2a3481602ab795567ef3bae32bfcbe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `050c649231a7efd609004f4471c68727af2a3481602ab795567ef3bae32bfcbe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `050c649231a7efd609004f4471c68727af2a3481602ab795567ef3bae32bfcbe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/os/kernel/ipc/ipc_syscall_handoff_spec.spl
mirror: doc/06_spec/unit/os/kernel/ipc/ipc_syscall_handoff_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/ipc/ipc_syscall_handoff_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/ipc/ipc_syscall_handoff_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/ipc/ipc_syscall_handoff_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/kernel/ipc/ipc_syscall_handoff_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocking recv records the current task as a port waiter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/ipc/ipc_syscall_handoff_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'send unblocks the first waiting receiver and consumes one waiter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
