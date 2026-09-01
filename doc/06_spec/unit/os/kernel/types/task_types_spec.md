# @manual: primary

> Purpose: Prove that TaskId.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that TaskId.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-002 |
| Category | Runtime |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/unit/os/kernel/types/task_types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that TaskId.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-OS-KERNEL-001
doc/01_research/local/REQ-OS-KERNEL-001.md
doc/03_plan/sys_test/REQ-OS-KERNEL-001.md
doc/04_architecture/REQ-OS-KERNEL-001.md
doc/05_design/REQ-OS-KERNEL-001.md

## Scenarios

### TaskId

#### stores the task identifier

- Verify: stores the task identifier
   - Expected: id.id equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: stores the task identifier")
val id = TaskId(id: 1)
expect(id.id).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### supports zero id

- Verify: supports zero id
   - Expected: id.id equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: supports zero id")
val id = TaskId(id: 0)
expect(id.id).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### supports large id

- Verify: supports large id
   - Expected: id.id equals `999999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: supports large id")
val id = TaskId(id: 999999)
expect(id.id).to_equal(999999)  # oracle: 999999 — named expected value from the requirement
```

</details>

#### can compare two equal ids

- Verify: can compare two equal ids
   - Expected: a.id equals `b.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: can compare two equal ids")
val a = TaskId(id: 42)
val b = TaskId(id: 42)
expect(a.id).to_equal(b.id)
```

</details>

#### can distinguish different ids

- Verify: can distinguish different ids
   - Expected: same is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: can distinguish different ids")
val a = TaskId(id: 1)
val b = TaskId(id: 2)
val same = a.id == b.id
expect(same).to_equal(false)
```

</details>

### TaskState

### Ready

#### can be constructed

- Verify: can be constructed
   - Expected: is_ready is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: can be constructed")
val state = TaskState.Ready
val is_ready = match state:
    TaskState.Ready: true
    _: false
expect(is_ready).to_equal(true)
```

</details>

### Running

#### can be constructed

- Verify: can be constructed
   - Expected: is_running is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: can be constructed")
val state = TaskState.Running
val is_running = match state:
    TaskState.Running: true
    _: false
expect(is_running).to_equal(true)
```

</details>

### Blocked

#### can be constructed with IpcRecv reason

- Verify: can be constructed with IpcRecv reason
   - Expected: is_blocked is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: can be constructed with IpcRecv reason")
val reason = BlockReason.IpcRecv(port: 5)
val state = TaskState.Blocked(reason: reason)
val is_blocked = match state:
    TaskState.Blocked(reason): true
    _: false
expect(is_blocked).to_equal(true)
```

</details>

#### can be constructed with Sleep reason

- Verify: can be constructed with Sleep reason
   - Expected: is_blocked is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: can be constructed with Sleep reason")
val reason = BlockReason.Sleep(until_ns: 1000000)
val state = TaskState.Blocked(reason: reason)
val is_blocked = match state:
    TaskState.Blocked(reason): true
    _: false
expect(is_blocked).to_equal(true)
```

</details>

### Zombie

#### can be constructed

- Verify: can be constructed
   - Expected: is_zombie is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: can be constructed")
val state = TaskState.Zombie
val is_zombie = match state:
    TaskState.Zombie: true
    _: false
expect(is_zombie).to_equal(true)
```

</details>

### TaskPriority

### Realtime

#### can be constructed

- Verify: can be constructed
   - Expected: is_rt is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: can be constructed")
val prio = TaskPriority.Realtime
val is_rt = match prio:
    TaskPriority.Realtime: true
    _: false
expect(is_rt).to_equal(true)
```

</details>

### High

#### can be constructed

- Verify: can be constructed
   - Expected: is_high is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: can be constructed")
val prio = TaskPriority.High
val is_high = match prio:
    TaskPriority.High: true
    _: false
expect(is_high).to_equal(true)
```

</details>

### Normal

#### can be constructed

- Verify: can be constructed
   - Expected: is_normal is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: can be constructed")
val prio = TaskPriority.Normal
val is_normal = match prio:
    TaskPriority.Normal: true
    _: false
expect(is_normal).to_equal(true)
```

</details>

### Low

#### can be constructed

- Verify: can be constructed
   - Expected: is_low is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: can be constructed")
val prio = TaskPriority.Low
val is_low = match prio:
    TaskPriority.Low: true
    _: false
expect(is_low).to_equal(true)
```

</details>

### Idle

#### can be constructed

- Verify: can be constructed
   - Expected: is_idle is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: can be constructed")
val prio = TaskPriority.Idle
val is_idle = match prio:
    TaskPriority.Idle: true
    _: false
expect(is_idle).to_equal(true)
```

</details>

### BlockReason

#### IpcRecv carries port number

- Verify: IpcRecv carries port number
   - Expected: port_val equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: IpcRecv carries port number")
val reason = BlockReason.IpcRecv(port: 42)
val port_val = match reason:
    BlockReason.IpcRecv(port): port
    _: 0
expect(port_val).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### IpcSend carries port number

- Verify: IpcSend carries port number
   - Expected: port_val equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: IpcSend carries port number")
val reason = BlockReason.IpcSend(port: 7)
val port_val = match reason:
    BlockReason.IpcSend(port): port
    _: 0
expect(port_val).to_equal(7)  # oracle: 7 — named expected value from the requirement
```

</details>

#### Sleep carries timestamp

- Verify: Sleep carries timestamp
   - Expected: ts equals `5000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: Sleep carries timestamp")
val reason = BlockReason.Sleep(until_ns: 5000000)
val ts = match reason:
    BlockReason.Sleep(until_ns): until_ns
    _: 0
expect(ts).to_equal(5000000)  # oracle: 5000000 — named expected value from the requirement
```

</details>

#### PageFault carries faulting address

- Verify: PageFault carries faulting address
   - Expected: fault_addr equals `0xDEAD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: PageFault carries faulting address")
val reason = BlockReason.PageFault(addr: 0xDEAD)
val fault_addr = match reason:
    BlockReason.PageFault(addr): addr
    _: 0
expect(fault_addr).to_equal(0xDEAD)
```

</details>

#### Exit has no payload

- Verify: Exit has no payload
   - Expected: is_exit is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: Exit has no payload")
val reason = BlockReason.Exit
val is_exit = match reason:
    BlockReason.Exit: true
    _: false
expect(is_exit).to_equal(true)
```

</details>

### TaskContext

#### stores general-purpose registers

- Verify: stores general-purpose registers
   - Expected: ctx.rax equals `1`
   - Expected: ctx.rbx equals `2`
   - Expected: ctx.rcx equals `3`
   - Expected: ctx.rdx equals `4`
   - Expected: ctx.rsi equals `5`
   - Expected: ctx.rdi equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: stores general-purpose registers")
val ctx = TaskContext(
    rax: 1, rbx: 2, rcx: 3, rdx: 4,
    rsi: 5, rdi: 6, rbp: 7, rsp: 8,
    r8: 9, r9: 10, r10: 11, r11: 12,
    r12: 13, r13: 14, r14: 15, r15: 16,
    rip: 0x1000, rflags: 0x202,
    cs: 0x23, ss: 0x1B, fpu_state: 0
)
expect(ctx.rax).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(ctx.rbx).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(ctx.rcx).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(ctx.rdx).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(ctx.rsi).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(ctx.rdi).to_equal(6)  # oracle: 6 — named expected value from the requirement
```

</details>

#### stores stack and instruction pointers

- Verify: stores stack and instruction pointers
   - Expected: ctx.rbp equals `0xFFFF0000`
   - Expected: ctx.rsp equals `0xFFFF1000`
   - Expected: ctx.rip equals `0x401000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: stores stack and instruction pointers")
val ctx = TaskContext(
    rax: 0, rbx: 0, rcx: 0, rdx: 0,
    rsi: 0, rdi: 0, rbp: 0xFFFF0000, rsp: 0xFFFF1000,
    r8: 0, r9: 0, r10: 0, r11: 0,
    r12: 0, r13: 0, r14: 0, r15: 0,
    rip: 0x401000, rflags: 0x202,
    cs: 0x23, ss: 0x1B, fpu_state: 0
)
expect(ctx.rbp).to_equal(0xFFFF0000)
expect(ctx.rsp).to_equal(0xFFFF1000)
expect(ctx.rip).to_equal(0x401000)
```

</details>

### UserProcessImage

#### stores executable path, entry, and stack

- Verify: stores executable path, entry, and stack
   - Expected: image.binary_path equals `/sys/services/vfs`
   - Expected: image.entry equals `0x400000`
   - Expected: image.stack_top equals `0x4000000000`
   - Expected: user_process_image_segment_count(image) equals `0`
   - Expected: image.initial_sp equals `0x3fffffff80`
   - Expected: image.initial_stack_bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: stores executable path, entry, and stack")
val image = UserProcessImage(
    binary_path: "/sys/services/vfs",
    entry: 0x400000,
    stack_top: 0x4000000000,
    stack_size: 65536,
    argv: ["/sys/services/vfs"],
    envp: [],
    segments: [],
    segment_count: 0,
    file_bytes: [0x13.to_u8(), 0, 0, 0],
    initial_sp: 0x3fffffff80,
    initial_stack_bytes: [0x01.to_u8(), 0x02, 0x03, 0x04]
)
expect(image.binary_path).to_equal("/sys/services/vfs")
expect(image.entry).to_equal(0x400000)
expect(image.stack_top).to_equal(0x4000000000)
expect(user_process_image_segment_count(image)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(image.initial_sp).to_equal(0x3fffffff80)
expect(image.initial_stack_bytes.len()).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### stores loadable user segments

- Verify: stores loadable user segments
   - Expected: seg.virt_addr equals `0x400000`
   - Expected: seg.data.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: stores loadable user segments")
val seg = UserLoadSegment(
    virt_addr: 0x400000,
    mem_size: 4,
    file_size: 4,
    flags: 5,
    align: 0x1000,
    data: [0x13.to_u8(), 0, 0, 0]
)
expect(seg.virt_addr).to_equal(0x400000)
expect(seg.data.len()).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### stores segment selectors

- Verify: stores segment selectors
   - Expected: ctx.cs equals `0x08`
   - Expected: ctx.ss equals `0x10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: stores segment selectors")
val ctx = TaskContext(
    rax: 0, rbx: 0, rcx: 0, rdx: 0,
    rsi: 0, rdi: 0, rbp: 0, rsp: 0,
    r8: 0, r9: 0, r10: 0, r11: 0,
    r12: 0, r13: 0, r14: 0, r15: 0,
    rip: 0, rflags: 0x202,
    cs: 0x08, ss: 0x10, fpu_state: 0
)
expect(ctx.cs).to_equal(0x08)
expect(ctx.ss).to_equal(0x10)
```

</details>

#### stores rflags

- Verify: stores rflags
   - Expected: ctx.rflags equals `0x202`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: stores rflags")
val ctx = TaskContext(
    rax: 0, rbx: 0, rcx: 0, rdx: 0,
    rsi: 0, rdi: 0, rbp: 0, rsp: 0,
    r8: 0, r9: 0, r10: 0, r11: 0,
    r12: 0, r13: 0, r14: 0, r15: 0,
    rip: 0, rflags: 0x202,
    cs: 0, ss: 0, fpu_state: 0
)
expect(ctx.rflags).to_equal(0x202)
```

</details>

#### stores extended registers r8-r15

- Verify: stores extended registers r8-r15
   - Expected: ctx.r8 equals `100`
   - Expected: ctx.r9 equals `200`
   - Expected: ctx.r10 equals `300`
   - Expected: ctx.r11 equals `400`
   - Expected: ctx.r12 equals `500`
   - Expected: ctx.r13 equals `600`
   - Expected: ctx.r14 equals `700`
   - Expected: ctx.r15 equals `800`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: stores extended registers r8-r15")
val ctx = TaskContext(
    rax: 0, rbx: 0, rcx: 0, rdx: 0,
    rsi: 0, rdi: 0, rbp: 0, rsp: 0,
    r8: 100, r9: 200, r10: 300, r11: 400,
    r12: 500, r13: 600, r14: 700, r15: 800,
    rip: 0, rflags: 0,
    cs: 0, ss: 0, fpu_state: 0
)
expect(ctx.r8).to_equal(100)  # oracle: 100 — named expected value from the requirement
expect(ctx.r9).to_equal(200)  # oracle: 200 — named expected value from the requirement
expect(ctx.r10).to_equal(300)  # oracle: 300 — named expected value from the requirement
expect(ctx.r11).to_equal(400)  # oracle: 400 — named expected value from the requirement
expect(ctx.r12).to_equal(500)  # oracle: 500 — named expected value from the requirement
expect(ctx.r13).to_equal(600)  # oracle: 600 — named expected value from the requirement
expect(ctx.r14).to_equal(700)  # oracle: 700 — named expected value from the requirement
expect(ctx.r15).to_equal(800)  # oracle: 800 — named expected value from the requirement
```

</details>

#### stores fpu_state pointer

- Verify: stores fpu_state pointer
   - Expected: ctx.fpu_state equals `0xBEEF0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: stores fpu_state pointer")
val ctx = TaskContext(
    rax: 0, rbx: 0, rcx: 0, rdx: 0,
    rsi: 0, rdi: 0, rbp: 0, rsp: 0,
    r8: 0, r9: 0, r10: 0, r11: 0,
    r12: 0, r13: 0, r14: 0, r15: 0,
    rip: 0, rflags: 0,
    cs: 0, ss: 0, fpu_state: 0xBEEF0000
)
expect(ctx.fpu_state).to_equal(0xBEEF0000)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-OS-KERNEL-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4c578bb9edc71ae3e5a4e30d6cd6ab84ff9629d1388051341a8d2148e9f0c3fa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4c578bb9edc71ae3e5a4e30d6cd6ab84ff9629d1388051341a8d2148e9f0c3fa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4c578bb9edc71ae3e5a4e30d6cd6ab84ff9629d1388051341a8d2148e9f0c3fa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/os/kernel/types/task_types_spec.spl
mirror: doc/06_spec/unit/os/kernel/types/task_types_spec.md (current)
findings: 12 blockers: 1
  narrative=100 structure=70 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/os/kernel/types/task_types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/types/task_types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/types/task_types_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/os/kernel/types/task_types_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores the task identifier' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/types/task_types_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports zero id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/types/task_types_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports large id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/types/task_types_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can compare two equal ids' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/os/kernel/types/task_types_spec.spl:78:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can distinguish different ids' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/os/kernel/types/task_types_spec.spl:93:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can be constructed' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/os/kernel/types/task_types_spec.spl:103:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can be constructed' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/os/kernel/types/task_types_spec.spl:113:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can be constructed with IpcRecv reason' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/os/kernel/types/task_types_spec.spl:123:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can be constructed with Sleep reason' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
