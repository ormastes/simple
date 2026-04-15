# Remote Baremetal Completion Plan

**Date:** 2026-04-04  
**Status:** Draft  
**Scope:** Complete the remaining work to make remote baremetal execution a tighter, evidence-backed feature with explicit stable lanes and explicit host-aware lanes.

## 1. Current Classification

Remote baremetal execution is **partial, not experimental**.

Why it is partial:
- the core architecture exists and is real
- multiple adapters execute real work
- stable proof lanes already exist
- the remaining gaps are about lane completeness, compiled-mode proof quality, host capability gating, and unfinished targets

Why it is not experimental:
- this is not a speculative code surface
- it already has working adapters, build flows, and passing proof specs
- README qualification is about uneven lane maturity, not about feature existence

## 2. Completion Target

The feature is complete when the repo can truthfully state:

> Remote baremetal execution provides stable compiled execution lanes for QEMU reference targets and supported host-aware hardware lanes, with capability detection, deterministic result channels, per-lane acceptance tests, and published lane status.

This does **not** require every hardware board to be always available.

It **does** require:
- stable reference lanes that run in compiled mode
- deterministic result collection per lane
- explicit capability reporting instead of ambiguous skip/pass outcomes
- authoritative lane ownership and acceptance criteria
- a published support matrix with stable, host-aware, and in-progress states

## 3. Problems To Close

### 3.1 Compiled-mode proof is not the default authoritative evidence

Current issue:
- some summaries still report `duration_ms: 0`
- interpreter-mode execution proves load/parse but not true remote execution cost or correctness

Completion requirement:
- every authoritative lane must have one compiled-mode execution proof
- interpreter-only specs may remain, but only as fast structural checks

### 3.2 Stable and host-aware lanes are not sharply separated in status reporting

Current issue:
- stable QEMU lanes, transport checks, and host-dependent hardware execution are all discussed together

Completion requirement:
- classify every lane into exactly one of:
  - `stable`
  - `host-aware`
  - `transport-only`
  - `in-progress`

### 3.3 Result channels are inconsistent across targets

Current issue:
- some lanes rely on semihost output
- some use debugger reads
- some use board-specific probe output

Completion requirement:
- define one primary result channel and one fallback per lane
- avoid ad hoc proof logic inside individual specs

### 3.4 Hardware capability detection is fragmented

Current issue:
- probes, permissions, board presence, and host setup are detected in multiple specs

Completion requirement:
- centralize capability detection and status normalization
- every host-aware lane must emit one normalized status object before execution

### 3.5 Two target areas are still incomplete

Open targets:
- GHDL RV32 mailbox lane
- ZedBoard / FPGA JTAG-connected execution lane

These remain the biggest blockers to a cleaner support matrix.

## 4. Final Lane Model

### 4.1 Stable Lanes

These must run in CI or controlled local verification without physical hardware:

- QEMU RV32 semihost ELF
- QEMU ARM semihost or GDB-managed execution
- x86_64 baremetal boot lane

Acceptance:
- compiled mode only
- deterministic output or exit semantics
- no dependence on USB probes
- explicit runtime and duration capture

### 4.2 Host-Aware Hardware Lanes

These are real supported features, but availability depends on probes, permissions, and boards:

- CH32V307 via `wlink`
- STM32H7 via OpenOCD
- STM32H7 via TRACE32

Acceptance:
- normalized capability probe
- deterministic execution result channel
- skip only for missing prerequisites
- fail on execution regressions once prerequisites are satisfied

### 4.3 Transport-Only Lanes

These verify debugger or upload plumbing, not authoritative workload execution:

- raw RV32 injected run-control
- memory/register readback probes
- low-level debugger connectivity matrix

Acceptance:
- keep separate from stable workload proof
- never use these lanes as the sole justification for “remote execution works”

### 4.4 In-Progress Lanes

- GHDL RV32 mailbox lane
- ZedBoard / FPGA JTAG execution

Acceptance:
- clearly labeled incomplete
- no README promotion until they gain authoritative compiled execution proof

## 5. Architecture Work

### 5.1 Add a central lane descriptor

Introduce a normalized lane descriptor in the remote execution stack:

Required fields:
- lane id
- target arch
- adapter kind
- proof class
- primary result channel
- fallback result channel
- capability probe function
- authoritative spec path
- status classification

Suggested location:
- `src/lib/nogc_sync_mut/debug/remote/exec/`

Outcome:
- all lane metadata becomes machine-readable
- docs and test reports can use the same source of truth

### 5.2 Add normalized capability reporting

Create one shared capability report model for:
- command presence
- board presence
- permission failures
- timeout failures
- unsupported host configuration

Required statuses:
- `ready`
- `skip_missing_tool`
- `skip_missing_board`
- `blocked_permissions`
- `blocked_host_config`
- `failed_runtime`

Outcome:
- host-aware skips stop looking like silent pass cases
- reports become comparable across CH32, OpenOCD, TRACE32, and GHDL

### 5.3 Separate runner orchestration from lane-specific result parsing

Current direction should become explicit:
- common runner handles build, upload, timeout, and lifecycle
- lane adapter owns only probe-specific control
- result decoding should be per result-channel strategy, not copied per spec

Result strategies to standardize:
- semihost text
- exit code
- RAM sentinel buffer
- register readback
- debugger console pattern

## 6. Implementation Phases

### Phase 1. Stabilize authoritative compiled proof

Goal:
- make compiled-mode proof the default evidence for stable and host-aware lanes

Tasks:
- add compiled-mode execution wrappers where specs still run through interpreter-only glue
- capture real elapsed time for authoritative lanes
- update summary/report logic so `duration_ms` reflects executed runs

Exit criteria:
- QEMU RV32 stable lane reports non-zero duration
- CH32 authoritative execution reports non-zero duration when hardware is present
- STM32H7 authoritative execution reports non-zero duration when hardware is present

### Phase 2. Centralize lane capability detection

Goal:
- stop duplicating host-tool and board checks across specs

Tasks:
- extract probe/tool detection from specs into shared remote execution helpers
- normalize `wlink`, OpenOCD, TRACE32, QEMU, and GHDL capability checks
- expose a printable lane status summary

Exit criteria:
- CH32, STM32H7, TRACE32, GHDL, and QEMU use the same capability-report shape
- specs consume normalized lane status instead of ad hoc strings

### Phase 3. Standardize result channels

Goal:
- every lane has a deterministic success channel

Required primary channels:
- QEMU RV32: semihost output or exit code
- QEMU ARM: semihost output or debugger stop state
- CH32V307: RAM sentinel or register readback
- STM32H7/OpenOCD: RAM sentinel or register readback
- TRACE32: memory/register verification
- GHDL: semihost output first, mailbox second

Tasks:
- define result packet conventions for shared workloads
- make workload fixtures write a known result code and optional checksum
- ensure adapters read the same canonical result structure

Exit criteria:
- one shared workload fixture can prove success on all supported lanes
- lane success no longer depends on lane-specific text scraping alone

### Phase 4. Promote CH32 and STM32 hardware lanes

Goal:
- make the real-hardware lanes reproducible and clearly supported

Tasks:
- keep CH32 `wlink` lane authoritative with RAM/register result proof
- keep STM32H7 shared-workload lane authoritative with OpenOCD readback proof
- add explicit environment/setup docs for permissions, probe naming, and board reset behavior
- add board power/reset helper integration if needed for repeatability

Exit criteria:
- CH32 lane: build -> flash/upload -> run -> read result -> assert success
- STM32H7 lane: build -> upload -> run -> read result -> assert success
- both lanes skip only on capability failure and fail on runtime regressions

### Phase 5. Finish GHDL mailbox lane

Goal:
- move GHDL from partial to fully supported simulation lane

Tasks:
- define mailbox protocol for target-to-host result transfer
- add fixture that writes structured pass/fail state into mailbox
- implement mailbox readout in the GHDL adapter

Exit criteria:
- GHDL has both semihost and mailbox-backed proof
- mailbox lane becomes the authoritative non-semihost simulation proof

### Phase 6. Either finish or explicitly quarantine FPGA lane

Goal:
- remove ambiguity around ZedBoard / FPGA support

Two allowed outcomes:
1. Finish it:
   - establish JTAG chain
   - add upload/run/result proof
   - classify as host-aware
2. Quarantine it:
   - move it to explicit `in-progress`
   - remove any wording that suggests active support

Exit criteria:
- FPGA lane is either supported with proof or clearly excluded from supported execution lanes

### Phase 7. Publish machine-readable lane status

Goal:
- make support claims auditable

Tasks:
- generate a lane matrix report from the lane descriptor source
- publish status into docs or report artifacts
- classify each lane by:
  - stable
  - host-aware
  - transport-only
  - in-progress

Exit criteria:
- README wording can be generated or checked against the lane matrix
- repo truth does not depend on manually synchronized prose

## 7. Test Plan

### 7.1 Stable authoritative lanes

Must remain green:
- `test/integration/remote_jit/qemu_rv32_library_semihost_spec.spl`
- `test/feature/app/remote_jit/qemu_rv32_jit_e2e_spec.spl`
- `test/integration/remote_jit/qemu_arm_composite_runner_spec.spl`

### 7.2 Host-aware authoritative lanes

Must skip cleanly when unavailable and fail on real regressions when available:
- `test/integration/remote_jit/ch32v307_composite_runner_spec.spl`
- `test/integration/remote_jit/ch32v307_composite_runner_path_spec.spl`
- `test/integration/remote_jit/stm32h7_composite_runner_spec.spl`
- TRACE32-backed STM32H7 E2E spec

### 7.3 Transport-only lanes

Must never be used as authoritative workload proof:
- `test/integration/remote_jit/qemu_rv32_raw_injected_regression_spec.spl`
- `test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl`

### 7.4 In-progress lanes

Required before promotion:
- GHDL mailbox-backed result spec
- FPGA JTAG execution spec

## 8. NFR Targets

### Reliability

- no silent false-pass on missing hardware
- stable lanes reproducible across two consecutive runs
- host-aware lanes report deterministic skip reason

### Performance

- authoritative reports capture actual runtime duration
- capability probe should complete in under 3 seconds for absent tools
- hardware lane timeout defaults should be lane-specific and documented

### Maintainability

- new boards should plug in by adding one adapter and one lane descriptor
- common result parsing must not be duplicated across specs
- docs should be generated from lane metadata where feasible

## 9. Recommended Public Classification After Completion

After Phases 1 through 5 are complete:

- **Stable:** QEMU RV32, QEMU ARM, x86_64 baremetal
- **Host-aware supported:** CH32V307, STM32H7/OpenOCD, STM32H7/TRACE32
- **Supported simulation:** GHDL RV32
- **In progress or excluded:** ZedBoard / FPGA until real execution proof exists

At that point, README wording can move from:
- `implemented with qualifiers`

to:
- `stable reference lanes plus host-aware hardware lanes`

without overclaiming universal board coverage.

## 10. Immediate Next Steps

1. Add shared lane descriptor and capability report types in `remote/exec/`.
2. Convert authoritative lane reports to compiled-mode duration capture.
3. Standardize result packets for shared workloads.
4. Promote CH32 and STM32 result verification to canonical RAM/register proof.
5. Finish GHDL mailbox execution or explicitly keep it partial.
6. Decide whether ZedBoard is a near-term supported lane or a quarantined in-progress lane.
