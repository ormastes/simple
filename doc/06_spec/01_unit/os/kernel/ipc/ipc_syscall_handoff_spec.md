# IPC Syscall Handoff Specification

> This unit spec proves the SimpleOS IPC syscall handoff path used by user-mode syscalls and scheduler wakeups. A blocking receive must stage the current task as a port waiter, and a send to that port must unblock and consume exactly one waiting receiver.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# IPC Syscall Handoff Specification

This unit spec proves the SimpleOS IPC syscall handoff path used by user-mode syscalls and scheduler wakeups. A blocking receive must stage the current task as a port waiter, and a send to that port must unblock and consume exactly one waiting receiver.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #simpleos-ipc-syscall-handoff |
| Category | SimpleOS / IPC / Scheduler |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/01_unit/os/kernel/ipc/ipc_syscall_handoff_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This unit spec proves the SimpleOS IPC syscall handoff path used by user-mode
syscalls and scheduler wakeups. A blocking receive must stage the current task
as a port waiter, and a send to that port must unblock and consume exactly one
waiting receiver.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/01_research/local/multicore_green.md

## Syntax

Run the IPC handoff proof:

```sh
src/compiler_rust/target/debug/simple test test/01_unit/os/kernel/ipc/ipc_syscall_handoff_spec.spl --mode=interpreter --clean
```

## Examples

The send scenario covers the regression where the IPC syscall wrapper reached
the scheduler unblock path but did not complete the waiter-consumption handoff
under the interpreter. It now calls the explicit CPU-aware unblock path and
verifies the port waiter list is empty after the send.

## Scenarios

### IPC syscall handoff

#### blocking recv records the current task as a port waiter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- blocking recv records the current task as a port waiter
- Create a scheduler, IPC manager, and receiver-owned port
- Invoke blocking IPC receive on an empty port
- Verify the current task is staged as the port waiter
   - Expected: state.result.value equals `0`
   - Expected: has_waiter is true
   - Expected: task_id.id equals `receiver.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("blocking recv records the current task as a port waiter")
step("Create a scheduler, IPC manager, and receiver-owned port")
var scheduler = Scheduler.new()
var ipc = IpcManager.new()
val receiver = scheduler.get_current()
val port = ipc.create_port(receiver, "ipc_blocking_recv")

step("Invoke blocking IPC receive on an empty port")
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

step("Verify the current task is staged as the port waiter")
expect(state.result.value).to_equal(0)
val waiter = state.ipc.get_first_waiter(port.id)
val has_waiter = waiter != nil
expect(has_waiter).to_equal(true)
if waiter != nil:
    val task_id = waiter
    expect(task_id.id).to_equal(receiver.id)
```

</details>

#### legacy zero-length send remains legacy when arg1 names a caller-owned port

- legacy zero-length send remains legacy when arg1 names a caller-owned port
- Create a scheduler, IPC manager, and a waiting receiver
- Send a zero-length legacy message to the receiver-owned port
- Verify the send succeeds, consumes one waiter, and retains legacy metadata
   - Expected: state.result.value equals `0`
   - Expected: state.ipc.get_first_waiter(port.id) equals `nil`
   - Expected: delivered.payload.len() equals `0`
   - Expected: header.src_port equals `0u64`
   - Expected: header.method equals `source.id.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("legacy zero-length send remains legacy when arg1 names a caller-owned port")
step("Create a scheduler, IPC manager, and a waiting receiver")
var scheduler = Scheduler.new()
var ipc = IpcManager.new()
val receiver = TaskId(id: 99)
val port = ipc.create_port(receiver, "ipc_send_wake")
val source = ipc.create_port(TaskId(id: 0), "ipc_send_source")
ipc.add_waiter(port, receiver)

step("Send a zero-length legacy message to the receiver-owned port")
val state = _handle_ipc_send_state(
    SyscallArgs(
        id: 20,
        arg0: port.id,
        arg1: source.id,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    ipc
)

step("Verify the send succeeds, consumes one waiter, and retains legacy metadata")
expect(state.result.value).to_equal(0)
expect(state.ipc.get_first_waiter(port.id)).to_equal(nil)
val delivered = state.ipc.recv_owned(receiver, port)
expect(delivered.payload.len()).to_equal(0)
val header = delivered.header.unwrap()
expect(header.src_port).to_equal(0u64)
expect(header.method).to_equal(source.id.to_u32())
```

</details>

#### frozen arg4 tag selects copied service traffic

- frozen arg4 tag selects copied service traffic
- Create a caller-owned named source and a receiving port
- Send an empty copied reply with the frozen tag
- Verify the copied ABI preserves the claimed source port
   - Expected: state.result.value equals `0`
   - Expected: delivered.payload.len() equals `0`
   - Expected: header.src_port equals `source.id`
   - Expected: header.method equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("frozen arg4 tag selects copied service traffic")
step("Create a caller-owned named source and a receiving port")
var scheduler = Scheduler.new()
var ipc = IpcManager.new()
val receiver = TaskId(id: 99)
val port = ipc.create_port(receiver, "ipc_tagged_destination")
val source = ipc.create_port(TaskId(id: 0), "ipc_tagged_source")

step("Send an empty copied reply with the frozen tag")
val state = _handle_ipc_send_state(
    SyscallArgs(
        id: 20,
        arg0: port.id,
        arg1: source.id,
        arg2: 0,
        arg3: 0,
        arg4: IPC_COPIED_SERVICE_TAG,
        arg5: 0
    ),
    scheduler,
    ipc
)

step("Verify the copied ABI preserves the claimed source port")
expect(state.result.value).to_equal(0)
val delivered = state.ipc.recv_owned(receiver, port)
expect(delivered.payload.len()).to_equal(0)
val header = delivered.header.unwrap()
expect(header.src_port).to_equal(source.id)
expect(header.method).to_equal(0u32)
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

- **Requirements:** `doc/02_requirements/feature/multicore_green.md`
- **Plan:** `doc/03_plan/sys_test/multicore_green.md`
- **Design:** `doc/05_design/multicore_green.md`
- **Research:** `doc/01_research/local/multicore_green.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5add0838a3affe5f20db5a7b96c7fedffbe9bbb944d3fad72d9032792dba2c1e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5add0838a3affe5f20db5a7b96c7fedffbe9bbb944d3fad72d9032792dba2c1e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5add0838a3affe5f20db5a7b96c7fedffbe9bbb944d3fad72d9032792dba2c1e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/kernel/ipc/ipc_syscall_handoff_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/ipc/ipc_syscall_handoff_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/ipc/ipc_syscall_handoff_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/ipc/ipc_syscall_handoff_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/ipc/ipc_syscall_handoff_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/ipc/ipc_syscall_handoff_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocking recv records the current task as a port waiter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/ipc/ipc_syscall_handoff_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'legacy zero-length send remains legacy when arg1 names a caller-owned port' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/ipc/ipc_syscall_handoff_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'frozen arg4 tag selects copied service traffic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
