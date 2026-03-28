# Remote Baremetal Remaining Work Without TRACE32

**Date:** 2026-03-24  
**Status:** Active  
**Scope:** Remaining repo-side remote baremetal and remote-JIT work excluding all TRACE32 / PowerView execution work.

---

## Summary

This plan excludes TRACE32 entirely.

Current state:

- host shared workload is green
- STM32H7 shared hardware workload is green
- QEMU RV32 stable ELF/shared-workload lane is green
- QEMU RV32 low-level GDB memory transport is green in `test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl`
- CH32 direct `wlink` hardware checks are green

Remaining work is now concentrated in:

1. CH32V307 shared-workload execution in the composite runner
2. optional recovery of raw RV32 injected execution as a separate run-control track
3. cleanup of remote/JIT test noise that obscures real failures

The stable proof lanes and the low-level transport lanes must remain separate.

---

## Backend Proof Model

### Host

Authoritative proof:

- `test/integration/remote_jit/baremetal_library_host_spec.spl`

This remains the fast semantic reference for the shared baremetal library workload.

### STM32H7

Authoritative proof:

- `test/integration/remote_jit/stm32h7_composite_runner_spec.spl`

This is the reference real-hardware shared-workload lane.

### QEMU RV32

Authoritative stable execution proof:

- `test/integration/remote_jit/qemu_rv32_library_semihost_spec.spl`
- `test/feature/app/remote_jit/qemu_rv32_jit_e2e_spec.spl`

Authoritative low-level transport proof:

- `test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl`

Non-authoritative integration smoke:

- `test/integration/remote_jit/qemu_rv32_composite_runner_spec.spl`

The integration smoke is only a prerequisite/fixture guard. It must not claim stable injected execution.

### CH32V307

Current proof:

- `test/integration/remote_jit/ch32v307_composite_runner_spec.spl`
- `test/feature/app/remote_jit/ch32v307_jit_e2e_spec.spl`

Currently proven:

- probe discovery
- RAM write/readback
- register access
- shared workload fixture reuse

Not yet proven:

- full shared-workload execution through the composite runner

---

## Implementation Plan

### 1. Finish CH32 composite-runner execution

Use direct `wlink` as the only execution backend.

Implementation rules:

- do not revive any stale CH32 adapter import path
- do not add a speculative generic backend before one direct execution path is green
- keep the shared target fixture:
  - `test/fixtures/remote_jit/baremetal_lib_workload_main.spl`

Execution model:

- compile the shared target fixture for the CH32 target
- load and run it through direct `wlink`
- verify success through a deterministic target result channel

Default result channel:

1. register readback after execution
2. RAM sentinel/result buffer after execution

Do not depend on semihosting for CH32 unless tooling proves it is reliable.

Acceptance:

- `test/integration/remote_jit/ch32v307_composite_runner_spec.spl` must execute the shared workload, not just perform readiness checks

### 2. Keep RV32 stable lane authoritative

Do not make raw injected execution the main RV32 proof lane.

The main green path remains:

- stable ELF/shared-workload execution
- low-level transport proof in `remote_baremetal_runtime_spec.spl`

Rules:

- keep `qemu_rv32_jit_e2e_spec.spl` focused on stable workload proof
- keep `qemu_rv32_composite_runner_spec.spl` as a lightweight integration smoke only
- do not let raw MI run-control instability block the RV32 product path

### 3. Recover raw RV32 injected execution only as a separate track

This is optional follow-up work after the main green path stays stable.

Recover it in isolation:

- add a focused MI run-control regression helper/spec
- cover:
  - resume
  - stop or halt
  - register readback after stop

Rules:

- do not combine this recovery with the main shared-workload proof
- do not rely on it for repo-wide “RV32 is working” status

### 4. Reduce remote/JIT noise

Limit cleanup to narrow improvements that increase signal:

- reduce interpreter export-warning noise during remote/JIT spec loads where feasible
- reduce duplicated wording and stale claims across RV32 specs
- keep test database lock/parse warnings out of scope unless they directly block these specs

This is not a broad logging or test DB redesign.

---

## Test Plan

Required green tests:

- `test/integration/remote_jit/baremetal_library_host_spec.spl`
- `test/integration/remote_jit/stm32h7_composite_runner_spec.spl`
- `test/integration/remote_jit/qemu_rv32_library_semihost_spec.spl`
- `test/feature/app/remote_jit/qemu_rv32_jit_e2e_spec.spl`
- `test/integration/remote_jit/qemu_rv32_composite_runner_spec.spl`
- `test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl`
- `test/integration/remote_jit/ch32v307_composite_runner_spec.spl`
- `test/feature/app/remote_jit/ch32v307_jit_e2e_spec.spl`

Required next acceptance:

- CH32 composite-runner spec must move from hardware-control proof to real shared-workload execution

Deferred acceptance:

- raw RV32 injected execution may be recovered later, but it is not required for the main green path

---

## Assumptions

- TRACE32 / PowerView execution is explicitly out of scope for this plan
- STM32H7 is the reference successful real-hardware shared-workload implementation
- QEMU RV32 stable ELF/shared-workload execution is the authoritative RISC-V proof for now
- CH32 direct `wlink` control is the only valid base for further CH32 implementation
- the next engineering priority after this doc is CH32 shared-workload execution in the composite runner
