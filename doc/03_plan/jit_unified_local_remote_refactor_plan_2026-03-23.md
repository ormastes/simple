# Unified Local + Remote JIT Refactor Plan

**Date:** 2026-03-23  
**Status:** In Progress  
**Scope:** Pure Simple JIT runner refactor to share compilation, binary layout, memory mapping, and execution orchestration across local and remote backends, starting with STM32H7.

---

## Goal

Unify JIT around one shared pipeline:

1. compile source to target binary bytes
2. plan binary placement in a backend-specific memory layout
3. load bytes through a backend-specific binary interface
4. prepare registers, stack, and return/halt trampoline
5. execute and collect result

The current repo duplicates too much of this logic across:

- local vs remote JIT
- arm vs riscv vs x86
- generic remote manager vs target-specific runner code

That duplication is causing repeated drift and breakage.

---

## Design Rules

### 1. One shared orchestration path

There should not be separate orchestration logic for:

- local JIT runner
- remote JIT runner
- STM32H7 special-case runner
- QEMU special-case runner

There should be one shared JIT runner that delegates only the backend-specific parts.

### 2. Shared binary interface

Both local and remote backends must implement the same conceptual interface:

- write code bytes
- read code bytes
- write register
- read register
- resume
- wait for halt/return

Local and remote differ in the implementation, not in the orchestration contract.

### 3. Shared memory layout planner

Memory mapping logic must be shared.

Local:

- may expand memory or allocate executable memory dynamically

Remote:

- must fit inside fixed target memory limits
- must fail early if requested layout exceeds target capacity
- must not silently expand

### 4. Shared architecture helpers

ARM, RISC-V, and x86 must share one structure for:

- entry-point adjustment
- return/halt trampoline encoding
- register mapping
- stack/register setup conventions

---

## Shared Layers

### JIT types

Create `src/lib/nogc_sync_mut/jit/jit_types.spl` with:

- `JitBackendKind`
- `JitMemoryLimits`
- `JitBinary`
- `JitLayoutPlan`

### JIT layout

Create `src/lib/nogc_sync_mut/jit/jit_layout.spl` with:

- fixed-layout planning for remote targets
- helper to append halt trampolines
- entry/return PC helpers

### JIT backend interface

Follow one conceptual interface:

- `load_binary`
- `verify_binary`
- `write_register`
- `read_register`
- `resume`
- `wait_halt`

Pure Simple may continue implementing this via closures, but the shape must stay shared.

---

## Refactor Order

### Phase 1. Extract shared JIT layout core

Status: started

- add shared JIT types
- add shared layout planning helpers
- use STM32H7 first

### Phase 2. Move STM32H7 to shared binary + layout flow

- STM32H7 remote runner should consume `JitBinary` + `JitLayoutPlan`
- stop hardcoding halt address / stack / return handling inline in test runner code
- keep OpenOCD telnet backend for STM32H7 for now because that path is currently more reliable than the GDB-MI path

### Phase 3. Extract hardware abstraction layer from STM32H7

- Status: in progress
- first extracted module:
  - `src/lib/nogc_sync_mut/jit/jit_hal_stm32h7.spl`
- after STM32H7 direct path is stable, extract the actual operations it uses into a backend HAL
- the HAL surface should stay minimal:
  - `connect`
  - `disconnect`
  - `write_code`
  - `read_code`
  - `write_register`
  - `read_register`
  - `resume`
  - `wait_halt`
- extract memory limits alongside the HAL so fixed-memory targets fail early and consistently
- do not design the HAL around speculative future features before STM32H7 proves the contract

### Phase 4. Fold QEMU ARM and QEMU RISC-V into the same runner

- make them consume the same layout planner and binary wrapper
- remove ad hoc per-target placement logic from the runner

### Phase 5. Introduce local backend on the same contract

- local JIT should use the same `JitBinary` and layout planning concepts
- local backend may mark memory limits as expandable

### Phase 6. Replace the duplicated runner branches

- `test_executor_composite.spl` should become thin dispatch only
- shared JIT execution should live in one place

---

## STM32H7 First Slice

The first implementation slice is intentionally narrow:

1. add shared JIT types and layout planning modules
2. make STM32H7 direct remote JIT path use:
   - `JitBinary`
   - `JitMemoryLimits.stm32h7_remote()`
   - `plan_binary_layout()`
   - shared halt trampoline append logic
3. keep current OpenOCD telnet control path until the shared runner is stable
4. once stable, extract the STM32H7 operations into the first hardware abstraction layer implementation

This gets STM32H7 onto the new architecture first, then other targets can follow the same shape.

---

## Test Refactor Direction

The next testing step is not another smoke-only target check.

The baremetal library tests should be refactored so the same logical test workload can run in two ways:

- host execution for fast library semantics validation
- remote/JIT execution for real target validation

The first target for that shared test shape should be STM32H7 hardware.

Initial candidates:

- `test/feature/app/remote_baremetal/remote_baremetal_library_spec.spl`
- `test/feature/baremetal/collections_qemu_spec.spl`
- allocator / collection workloads that can be reduced to a target-return or semihost result contract

Practical rule:

- keep host assertions as the source of truth for library behavior
- add a target-executable version of the same workload for remote/JIT lanes
- do not count assembly-only semihost smoke fixtures as completion for the library-test goal

### Immediate test tasks

1. extract one real library workload that is valid on both host and target
2. run that workload through the STM32H7 HAL-backed remote/JIT path on real hardware
3. only after STM32H7 is real and repeatable, move the same shared test shape to RISC-V

### Shared library test-set rule

- shared workload logic lives in:
  `test/feature/app/remote_baremetal/remote_baremetal_library_workload.spl`
- remote/JIT targets compile the same target fixture:
  `test/fixtures/remote_jit/baremetal_lib_workload_main.spl`
- host validation stays separate in:
  `test/integration/remote_jit/baremetal_library_host_spec.spl`
- hardware/emulator composite specs should use that same fixture instead of ad hoc `return 0` / `return 42` programs
- current proof target order:
  STM32H7 real hardware first, then QEMU RV32, then real RISC-V hardware

### Current shared workload status

- host shared workload:
  `test/integration/remote_jit/baremetal_library_host_spec.spl` passes
- STM32H7 real hardware shared workload:
  `test/integration/remote_jit/stm32h7_composite_runner_spec.spl` passes
- QEMU RV32 shared workload:
  `test/integration/remote_jit/qemu_rv32_composite_runner_spec.spl` is now interpreter-safe and passes as a blocked/skip-style transport check
  current live blocker on this host is lack of a target-aware RISC-V GDB
  (`riscv32-unknown-elf-gdb`, `riscv64-unknown-elf-gdb`, or `gdb-multiarch`)
  so QEMU physical memory write mode cannot be used reliably
- QEMU RV32 semihost library workload:
  `test/integration/remote_jit/qemu_rv32_library_semihost_spec.spl` passes on this host
  and proves a real RV32 baremetal library workload through the stable ELF lane
- CH32V307 real hardware direct-control workload:
  `test/integration/remote_jit/ch32v307_composite_runner_spec.spl` now uses direct `wlink`
  instead of the stale adapter import path
  current proven operations are probe discovery, RAM write/readback, register dump,
  and reuse of the shared baremetal workload fixture
  full shared-workload execution on CH32V307 is still pending
- the remaining STM32H7 interpreter blocker was in `jit_util.spl`:
  `index_of()` was being treated as an integer in helper code, which triggered the documented runtime failure
  `semantic: type mismatch: cannot convert enum to int`
- STM32H7 shared workload is currently proven with a direct HAL-backed path and a temporary ARM32 stub compiler in the spec

---

## Current Known Risks

- the shared STM32H7 composite runner is now passing, but SRAM readback verify is still skipped because `read_code` is not interpreter-safe yet
- there are stale OpenOCD session risks when tests leak processes
- the older dedicated STM32H7 E2E spec is still unstable on SRAM/register readback and is not yet moved onto the new HAL path
- the current baremetal “library” coverage on hardware is still mostly smoke-oriented fixture execution, not a shared host+remote library test workload
- TRACE32 on this host is repo-ready but session-blocked:
  `/opt/t32/bin/pc_linux64/t32rem localhost port=20000 PING` times out with exit `124`
- GDB-MI and telnet startup behavior are still inconsistent enough that the telnet path remains the more practical STM32H7 control path for now

---

## Next Backend After STM32H7

After the STM32H7 hardware-backed library test shape is working, the next backend step should be RISC-V.

Order:

1. QEMU `riscv32` on the shared runner
2. fix the QEMU `riscv32` transport so the shared workload executes instead of skipping on blocked writes
3. real RISC-V hardware only after the QEMU path uses the same shared library test shape

Current CH32V307 note:

- the old adapter-based CH32 runner was stale and imported a non-existent adapter module
- the direct WCH-Link path is real on this host and should be the basis for the first CH32 HAL/backend
- full CH32 shared-workload execution remains a follow-up after direct control is stabilized

Practical note:

- the stable near-term RV32 proof lane is semihost ELF execution
- the still-broken lane is raw remote-JIT byte injection through QEMU GDB

The RISC-V objective is not another ELF/smoke check.
It is to make the same baremetal library test workload run through:

- host
- remote/JIT on STM32H7
- remote/JIT on `riscv32`

## Success Criteria

The refactor is successful when:

- STM32H7 shared JIT runner passes through shared `JitBinary` + `JitLayoutPlan`
- STM32H7 backend helpers live behind the first HAL module instead of inline runner code
- at least one baremetal library test workload runs both on host and on real STM32H7 hardware through the shared remote/JIT path
- QEMU ARM and QEMU RISC-V can move to the same layout/orchestration logic
- local JIT can consume the same binary/layout contract
- remote backends fail cleanly on fixed memory overflow
- runner code is backend-thin and no longer duplicates layout/trampoline logic
