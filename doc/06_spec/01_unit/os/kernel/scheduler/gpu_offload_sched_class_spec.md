# SimpleOS GPU-Offload Scheduling — Pure Decision Logic Specification

> [OS-DESIGN-ONLY] Boot-independent pure functions for the CPU/GPU offload model

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS GPU-Offload Scheduling — Pure Decision Logic Specification

[OS-DESIGN-ONLY] Boot-independent pure functions for the CPU/GPU offload model

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/scheduler/gpu_offload_sched_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

[OS-DESIGN-ONLY] Boot-independent pure functions for the CPU/GPU offload model
(#39, Gaps #4/#5). The SimpleOS kernel wiring is boot-blocked (freestanding
B1/B2 + bootstrap stage-2), so this pins ONLY the pure decisions the design adds
over the existing green scheduler + SOSIX substrate + memory_leveling capsule.

Grounds (design mirrors these existing files):
- sched_class_rank      src/os/kernel/scheduler/scheduler_algorithm.spl:26-35
- SchedulerPolicy       src/os/kernel/types/task_types.spl:49-57
- green_task_park       src/os/kernel/scheduler/green_task.spl:55-65
- process_queue EAGAIN  src/os/kernel/ipc/process_queue.spl:151-152
- seal-before-share     src/os/kernel/ipc/shared_dataset.spl:98
- queue_send sealed gate src/os/kernel/ipc/syscall_spm.spl:393-395
- memory_leveling pin   src/os/kernel/memory/memory_leveling.spl (pin_device/GPU-resident)

## Scenarios

### GPU-offload scheduling pure decision logic (OS-DESIGN-ONLY)

### Gap #4 sched-class rank (additive over scheduler_algorithm.spl:26-35)

#### places GpuOffload at the interactive/Fair tier

- places GpuOffload at the interactive/Fair tier


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("places GpuOffload at the interactive/Fair tier")
assert_equal(gpu_offload_sched_class_rank("GpuOffload"), 3)
assert_equal(gpu_offload_sched_class_rank("Fair"), 3)
```

</details>

#### never preempts RT or Deadline

- never preempts RT or Deadline


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never preempts RT or Deadline")
assert_true(gpu_offload_sched_class_rank("GpuOffload") > gpu_offload_sched_class_rank("RtFifo"))
assert_true(gpu_offload_sched_class_rank("GpuOffload") > gpu_offload_sched_class_rank("Deadline"))
```

</details>

#### is never starved below Idle

- is never starved below Idle


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is never starved below Idle")
assert_true(gpu_offload_sched_class_rank("GpuOffload") < gpu_offload_sched_class_rank("Idle"))
```

</details>

#### leaves existing class ranks unchanged

- leaves existing class ranks unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves existing class ranks unchanged")
assert_equal(gpu_offload_sched_class_rank("Internal"), 0)
assert_equal(gpu_offload_sched_class_rank("Deadline"), 1)
assert_equal(gpu_offload_sched_class_rank("RtFifo"), 2)
assert_equal(gpu_offload_sched_class_rank("Background"), 4)
assert_equal(gpu_offload_sched_class_rank("Idle"), 5)
```

</details>

### Gap #4 placement + backpressure fork

<details>
<summary>Advanced: offloads an eligible host-immutable op when the queue has room</summary>

#### offloads an eligible host-immutable op when the queue has room

- offloads an eligible host-immutable op when the queue has room


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("offloads an eligible host-immutable op when the queue has room")
assert_equal(gpu_offload_placement(true, true, 0, 1024), "offload")
```

</details>


</details>

#### stays on the CPU mirror when the op is ineligible

- stays on the CPU mirror when the op is ineligible


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stays on the CPU mirror when the op is ineligible")
assert_equal(gpu_offload_placement(false, true, 0, 1024), "cpu_mirror")
```

</details>

#### stays on the CPU mirror when the op mutates host state

- stays on the CPU mirror when the op mutates host state


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stays on the CPU mirror when the op mutates host state")
assert_equal(gpu_offload_placement(true, false, 0, 1024), "cpu_mirror")
```

</details>

#### signals backpressure when the bounded queue is full

- signals backpressure when the bounded queue is full


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("signals backpressure when the bounded queue is full")
assert_equal(gpu_offload_placement(true, true, 1024, 1024), "backpressure")
```

</details>

### Gap #4b memory_leveling integration

#### activates GPU offload only under the heterogeneous_device profile

- activates GPU offload only under the heterogeneous_device profile


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("activates GPU offload only under the heterogeneous_device profile")
assert_true(gpu_offload_profile_gate("heterogeneous_device"))
```

</details>

#### disables GPU offload under baremetal_static and simpleos_default

- disables GPU offload under baremetal_static and simpleos_default


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disables GPU offload under baremetal_static and simpleos_default")
assert_false(gpu_offload_profile_gate("baremetal_static"))
assert_false(gpu_offload_profile_gate("simpleos_default"))
```

</details>

#### pins the command-buffer page on submit and releases it on completion

- pins the command-buffer page on submit and releases it on completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins the command-buffer page on submit and releases it on completion")
assert_equal(gpu_offload_pin_lifecycle("submit"), "pin_device")
assert_equal(gpu_offload_pin_lifecycle("completed"), "keep")
```

</details>

#### releases the pin even on an unavailable (fallback) completion

- releases the pin even on an unavailable (fallback) completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("releases the pin even on an unavailable (fallback) completion")
assert_equal(gpu_offload_pin_lifecycle("unavailable"), "keep")
```

</details>

### Gap #5 sealed command-buffer protocol

#### seals a building buffer before it can be shared

- seals a building buffer before it can be shared


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("seals a building buffer before it can be shared")
assert_equal(sealed_cmd_buffer_next("building", "seal"), "sealed")
```

</details>

#### rejects enqueue of an unsealed buffer (seal-before-share)

- rejects enqueue of an unsealed buffer (seal-before-share)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects enqueue of an unsealed buffer (seal-before-share)")
assert_equal(sealed_cmd_buffer_next("building", "enqueue"), "rejected_unsealed")
```

</details>

#### rejects a write to a sealed buffer (immutability)

- rejects a write to a sealed buffer (immutability)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a write to a sealed buffer (immutability)")
assert_equal(sealed_cmd_buffer_next("sealed", "write"), "rejected_sealed")
```

</details>

#### runs seal -> enqueue -> submit -> complete to completion

- runs seal -> enqueue -> submit -> complete to completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs seal -> enqueue -> submit -> complete to completion")
val s1 = sealed_cmd_buffer_next("building", "seal")
val s2 = sealed_cmd_buffer_next(s1, "enqueue")
val s3 = sealed_cmd_buffer_next(s2, "submit")
val s4 = sealed_cmd_buffer_next(s3, "complete")
assert_equal(s4, "completed")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `8d49c0f4bb46cd3c252f828cdbb2fa9e74c02be6332f6d9ae8cc7dce1a0ea9e0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8d49c0f4bb46cd3c252f828cdbb2fa9e74c02be6332f6d9ae8cc7dce1a0ea9e0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8d49c0f4bb46cd3c252f828cdbb2fa9e74c02be6332f6d9ae8cc7dce1a0ea9e0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/kernel/scheduler/gpu_offload_sched_class_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/scheduler/gpu_offload_sched_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/scheduler/gpu_offload_sched_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/scheduler/gpu_offload_sched_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/scheduler/gpu_offload_sched_class_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'places GpuOffload at the interactive/Fair tier' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/scheduler/gpu_offload_sched_class_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never preempts RT or Deadline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/scheduler/gpu_offload_sched_class_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is never starved below Idle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
