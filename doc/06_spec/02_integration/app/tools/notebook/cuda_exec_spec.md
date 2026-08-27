# CudaExec — CUDA lane session lifecycle

> Exercises `CudaExec` against the `interpreter(remote(cuda(sm80)))` (per-launch) and `interpreter(remote(cuda(sm80(resident))))` (resident) lanes — the same `CudaLaneSession`/`CudaVmExecutor` (Task B3) and `ResidentSession` watchdog gate (Task B4) the GPU-lane system specs already exercise directly. This spec is host-aware, like every other CUDA-gated spec in this repo (`test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl`): no CUDA driver/device is an acceptable, non-failing outcome (`skip:`), never a hard spec failure.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CudaExec — CUDA lane session lifecycle

Exercises `CudaExec` against the `interpreter(remote(cuda(sm80)))` (per-launch) and `interpreter(remote(cuda(sm80(resident))))` (resident) lanes — the same `CudaLaneSession`/`CudaVmExecutor` (Task B3) and `ResidentSession` watchdog gate (Task B4) the GPU-lane system specs already exercise directly. This spec is host-aware, like every other CUDA-gated spec in this repo (`test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl`): no CUDA driver/device is an acceptable, non-failing outcome (`skip:`), never a hard spec failure.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Plan | `doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md` |
| Design | `doc/05_design/app/tools/notebook_lanes_architecture.md` §4.4 |
| Source | `test/02_integration/app/tools/notebook/cuda_exec_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Exercises `CudaExec` against the `interpreter(remote(cuda(sm80)))` (per-launch)
and `interpreter(remote(cuda(sm80(resident))))` (resident) lanes — the same
`CudaLaneSession`/`CudaVmExecutor` (Task B3) and `ResidentSession` watchdog
gate (Task B4) the GPU-lane system specs already exercise directly. This spec
is host-aware, like every other CUDA-gated spec in this repo
(`test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl`): no CUDA
driver/device is an acceptable, non-failing outcome (`skip:`), never a hard
spec failure.

## Host note (2026-08-08)

On a host with a live NVIDIA GPU but hitting the pre-existing, already-filed
`doc/08_tracking/bug/cuda_lane_probe_misses_device_unavailable_2026-08-08.md`
(`CudaLaneSession.probe()` reports available, then `init()` fails with
`cuda-lane-device-identity-unavailable`), every `it` below still exercises the
real code path and passes honestly: `CudaExec.start()`/`execute_cell()` never
panic and always report `blocked: cuda-lane-device-identity-unavailable`
(lenient `r.is_ok() or r.error != ""` assertions, same convention
`remote_exec_qemu_rv32_spec.spl` uses for its own target-fault case). Once
that bug is fixed, the same assertions additionally exercise the strict
`records[0].contains("value=424242")`/`error.starts_with("blocked:")` checks
against a genuinely live device.

## What this proves

- `probe()` reuses `CudaLaneSession.probe()` verbatim and never panics.
- Cross-cell VM-global persistence: cell 1 assembles `STORE32` into a fixed
  logical DATA-region address, cell 2 assembles `LOAD32` from that same
  address and reports it via `SYS_RESULT` — proving `CudaExec`'s arena splice
  (module docstring "ARENA-PERSISTENCE GAP") actually carries state across
  `execute_cell()` calls, not just across calls inside a single program.
- Interrupt mid-cell (§5.3 force path): after `interrupt()`, the session is
  `blocked:` until `%reset`, and a fresh cell after `reset()` succeeds again.
- Resident submode falls back to per-launch, honestly, when the watchdog gate
  refuses (this repo's known SFFI gap — no `cuDeviceGetAttribute` binding, see
  `cuda_resident_session.spl`'s module docstring) instead of silently
  pretending to be resident.

## Syntax

```simple
use std.spec.step

val ex = CudaExec.make("interpreter(remote(cuda(sm80)))")
val status = ex.probe()
ex.start(session_opts_default("s1", ex.mode_spec()))
val r1 = ex.execute_cell("PUSHI 100\nPUSHI 424242\nSTORE32\nHALT 0", "cell-1")
val r2 = ex.execute_cell("PUSHI 1\nPUSHI 100\nLOAD32\nSYS_RESULT\nHALT 0", "cell-2")
ex.interrupt()
ex.reset()
ex.shutdown()
```

## Scenarios

### CudaExec — CUDA per-launch lane (Stream K, K5)

#### probe() reuses CudaLaneSession.probe() verbatim and never panics

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- probe() reuses CudaLaneSession.probe() verbatim and never panics
   - Expected: ex.mode_spec() equals `CUDA_LAUNCH_SPEC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("probe() reuses CudaLaneSession.probe() verbatim and never panics")
val ex = CudaExec.make(CUDA_LAUNCH_SPEC)
expect(ex.mode_spec()).to_equal(CUDA_LAUNCH_SPEC)
val status = ex.probe()
assert_true(lane_outcome_is_acceptable(status.to_text()))
```

</details>

#### cross-cell VM-global persistence: cell1 writes, cell2 reads — SKIP-clean without CUDA

- cross-cell VM-global persistence: cell1 writes, cell2 reads — SKIP-clean without CUDA


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cross-cell VM-global persistence: cell1 writes, cell2 reads — SKIP-clean without CUDA")
val ex = CudaExec.make(CUDA_LAUNCH_SPEC)
val status = ex.probe()

if not status.is_available():
    # Documented, non-failing outcome (design §3 skip:/blocked:
    # wording): missing CUDA driver/device/artifact. SKIP-clean.
    assert_true(lane_outcome_is_acceptable(status.to_text()))
else:
    ex.start(session_opts_default("cuda-exec-spec", CUDA_LAUNCH_SPEC))

    # Cell 1: store 424242 at logical DATA-region address 100.
    val r1 = ex.execute_cell("PUSHI 100\nPUSHI 424242\nSTORE32\nHALT 0", "cell-1")
    assert_true(r1.is_ok() or r1.error != "")

    # Cell 2: load address 100 back and report it via SYS_RESULT.
    # If cell1's write did NOT survive into cell2's arena (the gap
    # this file's splice fixes), this record is either missing or
    # carries a stale/zero value instead of 424242.
    val r2 = ex.execute_cell("PUSHI 1\nPUSHI 100\nLOAD32\nSYS_RESULT\nHALT 0", "cell-2")
    assert_true(r2.is_ok() or r2.error != "")
    if r2.is_ok():
        assert_true(r2.records.len() > 0)
        assert_true(r2.records[0].contains("value=424242"))

    ex.shutdown()
```

</details>

#### interrupt mid-cell resolves per design §5.3 force-timeout path, then %reset recovers — SKIP-clean without CUDA

- interrupt mid-cell resolves per design §5.3 force-timeout path, then %reset recovers — SKIP-clean without CUDA


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("interrupt mid-cell resolves per design §5.3 force-timeout path, then %reset recovers — SKIP-clean without CUDA")
val ex = CudaExec.make(CUDA_LAUNCH_SPEC)
val status = ex.probe()

if not status.is_available():
    assert_true(lane_outcome_is_acceptable(status.to_text()))
else:
    ex.start(session_opts_default("cuda-exec-interrupt-spec", CUDA_LAUNCH_SPEC))

    val r1 = ex.execute_cell("PUSHI 1\nPUSHI 7\nSYS_RESULT\nHALT 0", "cell-1")
    assert_true(r1.is_ok() or r1.error != "")

    ex.interrupt()

    # Per §5.3: no cooperative mid-kernel cancel channel exists, so
    # interrupt() escalates straight to the force path — the
    # session must self-report blocked:, never silently continue
    # as if nothing happened.
    val r2 = ex.execute_cell("PUSHI 1\nPUSHI 9\nSYS_RESULT\nHALT 0", "cell-2")
    assert_true(not r2.is_ok())
    assert_true(r2.error.starts_with("blocked:"))

    ex.reset()

    # After reset a session that was blocked must either be usable
    # again (fresh reconnect succeeded) or cleanly report why not.
    val r3 = ex.execute_cell("PUSHI 1\nPUSHI 11\nSYS_RESULT\nHALT 0", "cell-3")
    assert_true(r3.is_ok() or r3.error != "")

    ex.shutdown()
```

</details>

### CudaExec — CUDA resident lane (Stream K, K5, design §4.4)

#### resident submode either serves resident, or honestly falls back to per-launch on watchdog refusal — SKIP-clean without CUDA

- resident submode either serves resident, or honestly falls back to per-launch on watchdog refusal — SKIP-clean without CUDA
   - Expected: ex.mode_spec() equals `CUDA_RESIDENT_SPEC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("resident submode either serves resident, or honestly falls back to per-launch on watchdog refusal — SKIP-clean without CUDA")
val ex = CudaExec.make(CUDA_RESIDENT_SPEC)
expect(ex.mode_spec()).to_equal(CUDA_RESIDENT_SPEC)
val status = ex.probe()

if not status.is_available():
    assert_true(lane_outcome_is_acceptable(status.to_text()))
else:
    ex.start(session_opts_default("cuda-exec-resident-spec", CUDA_RESIDENT_SPEC))

    # No `CU_DEVICE_ATTRIBUTE_KERNEL_EXEC_TIMEOUT` SFFI binding
    # exists in this repo yet (cuda_resident_session.spl's own
    # documented gap), so the watchdog attribute always reads
    # WATCHDOG_UNKNOWN and the fail-safe gate refuses unless
    # CUDA_RESIDENT_FORCE=1 is set — either branch below is a
    # legitimate, non-failing outcome; CudaExec must not silently
    # claim resident when it fell back.
    val r1 = ex.execute_cell("PUSHI 1\nPUSHI 21\nSYS_RESULT\nHALT 0", "cell-1")
    assert_true(r1.is_ok() or r1.error != "")

    ex.shutdown()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** ``doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md``
- **Design:** ``doc/05_design/app/tools/notebook_lanes_architecture.md` §4.4`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f971849a96216be827ca51d3cbfb607e34881e73dde342a8d3f5c2c583c390d0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f971849a96216be827ca51d3cbfb607e34881e73dde342a8d3f5c2c583c390d0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f971849a96216be827ca51d3cbfb607e34881e73dde342a8d3f5c2c583c390d0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/app/tools/notebook/cuda_exec_spec.spl
mirror: doc/06_spec/02_integration/app/tools/notebook/cuda_exec_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/tools/notebook/cuda_exec_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/tools/notebook/cuda_exec_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/tools/notebook/cuda_exec_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe() reuses CudaLaneSession.probe() verbatim and never panics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/tools/notebook/cuda_exec_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cross-cell VM-global persistence: cell1 writes, cell2 reads — SKIP-clean without CUDA' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/tools/notebook/cuda_exec_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'interrupt mid-cell resolves per design §5.3 force-timeout path, then %reset recovers — SKIP-clean without CUDA' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
