# RV64 User-Mode Exec Status Report — 2026-04-02

## Summary

This report captures the current state of the `rv64_user_mode_exec` effort.
The work has progressed from pure planning to concrete kernel-side runtime
contracts, but the end-to-end milestone is still **not complete**.

Current status:
- ELF-backed launch has a transitional kernel path.
- RV64 trap policy and syscall marshalling are implemented in Simple.
- The trap/runtime handoff is now explicit in code.
- Early RV64 boot now installs a bootstrap trap runtime.
- The actual low-level trap entry/return path is still missing.

The main blocker is unchanged:
- there is still no linked `_rv64_trap_vector` implementation that saves a
  real `Riscv64Context` trap frame, dispatches it, restores it, and returns
  with `sret`.

## What Was Done

### Documentation and planning

The repo now has a blocker-focused documentation chain for
`rv64_user_mode_exec`:
- `doc/01_research/local/rv64_user_mode_exec.md`
- `doc/01_research/domain/rv64_user_mode_exec.md`
- `doc/02_requirements/feature/rv64_user_mode_exec.md`
- `doc/02_requirements/nfr/rv64_user_mode_exec.md`
- `doc/03_plan/rv64_user_mode_exec.md`
- `doc/03_plan/agent_tasks/rv64_user_mode_exec.md`
- `doc/03_plan/sys_test/rv64_user_mode_exec.md`
- `doc/04_architecture/rv64_user_mode_exec.md`
- `doc/05_design/rv64_user_mode_exec.md`
- `doc/06_spec/app/os/feature/rv64_user_mode_exec_spec.spl`

Those docs define the current blocker correctly:
- RV64 true user-mode exec is the gating milestone.
- RV32, Linux boot, repo-native simulation, RTL/VHDL, and GUI OS remain
  downstream work.

### Launch/runtime groundwork

The userspace launch path has moved beyond placeholders:
- `spawn_binary(path, priority)` is wired through userlib, init, and kernel.
- known `/sys/services/*` and `/sys/apps/*` paths resolve to boot-packaged
  executable bytes.
- the kernel can validate those bytes structurally as RISC-V ELF and convert
  them into a transitional `UserProcessImage`.
- the scheduler has a separate `create_user_task(...)` path and stores RV64
  user handoff state explicitly.

Relevant files:
- `src/os/kernel/ipc/syscall.spl`
- `src/os/kernel/loader/executable_source.spl`
- `src/os/kernel/loader/process_image.spl`
- `src/os/kernel/scheduler/scheduler.spl`
- `src/os/kernel/types/task_types.spl`

### RV64 trap policy and syscall semantics

The architecture-side trap policy exists and is tested:
- kernel vs user initial `sstatus` setup is defined
- `scause` classification is implemented
- RV64 syscall register marshalling is implemented
- syscall result application updates `a0` and advances `sepc` by 4

Relevant file:
- `src/os/kernel/arch/riscv64/trap_model.spl`

### RV64 interrupt/runtime bridge

The interrupt layer now contains a real runtime-facing bridge instead of only
an extern placeholder:
- installed runtime state is explicit
- the dispatcher can run through installed scheduler / IPC / klog objects
- trap failures are reported through serial and kernel log
- a pointer-based in-place trap-frame bridge exists for the future vector path

Relevant files:
- `src/os/kernel/arch/riscv64/interrupt.spl`
- `src/os/kernel/arch/riscv64/trap_runtime.spl`
- `src/os/kernel/arch/riscv64/trap_frame.spl`

The trap-frame ABI is now explicit:
- stable RV64 saved-frame size
- stable per-field offsets matching `Riscv64Context`
- a future assembly vector can target this contract directly

### Early boot seam

The first real boot seam now installs the trap runtime:
- `Rv64Boot.save_boot_args(...)` installs a bootstrap trap runtime if one is
  not already present
- this moves runtime installation onto a real RV64 boot path instead of
  leaving it only in tests

Relevant file:
- `src/os/kernel/arch/riscv64/boot.spl`

## Verified So Far

Focused unit coverage now exists for:
- RV64 trap model semantics
- RV64 trap-frame layout contract
- installed trap runtime behavior
- pointer-based trap-frame dispatch bridge
- bootstrap runtime installation during RV64 boot argument capture
- scheduler user-task handoff
- transitional ELF / executable source path

Representative passing specs:
- `test/unit/os/kernel/arch/riscv64_trap_model_spec.spl`
- `test/unit/os/kernel/arch/riscv64_trap_frame_spec.spl`
- `test/unit/os/kernel/arch/riscv64_interrupt_spec.spl`
- `test/unit/os/kernel/arch/riscv64_boot_spec.spl`
- `test/unit/os/kernel/scheduler/scheduler_spec.spl`
- `test/unit/os/kernel/ipc/syscall_spec.spl`
- `test/unit/os/kernel/loader/executable_source_spec.spl`
- `test/unit/os/kernel/loader/process_image_spec.spl`

## What Still Should Be Done

### 1. Implement the real RV64 trap vector

Still required:
- define the linked `_rv64_trap_vector`
- save a full `Riscv64Context` trap frame
- load CSR values into the saved frame
- call the installed Simple-level trap-frame bridge
- restore registers from the updated frame
- return with `sret`

This is the single most important remaining step.

### 2. Prove true user-mode execution

After the vector exists:
- launch one ELF-backed RV64 user task
- reach U-mode from the scheduler/runtime path
- execute `ecall`
- dispatch through `syscall_handler(...)`
- resume user execution with updated `a0` and `sepc`
- exit cleanly

### 3. Replace staged proof executable content

The current executable-source path is still transitional:
- proof paths exist
- the launch ABI is real
- but the first proof payload still needs to become a real minimal RV64 user
  ELF that performs output / `GetPid` / `Exit`

### 4. Wire full boot/runtime composition

The boot seam currently installs a bootstrap runtime bundle, not the final
kernel runtime composition. Later work still needs:
- real scheduler construction
- real IPC manager construction
- real kernel log ownership
- one authoritative boot-time install path for the full runtime bundle

### 5. RV32 carryover

After RV64 true user-mode exec is proven:
- replicate the same trap/runtime model on RV32
- do not design a separate launch/runtime path

### 6. Downstream work still blocked

Blocked behind RV64 true user-mode exec:
- RV64 Linux boot
- repo-native simulator
- generated RV32/RV64 RTL from the hardware/VHDL path
- GUI full OS execution in the new simulator

## Why It Is Blocking

### No low-level trap entry/return artifact yet

The repo now has:
- trap policy
- trap-frame ABI
- runtime bundle
- pointer-based dispatch bridge

But it still does **not** have the thing that makes those contracts live on
hardware or QEMU:
- no `_rv64_trap_vector`
- no register save/restore path
- no `sret` return path

Without that, the kernel cannot prove real user-mode syscall round-trips.

### Build integration for OS-side assembly is not wired yet

Research during implementation found the likely future integration points:
- `src/os/build.sdn`
- `src/os/machine_profile.spl`
- `src/os/qemu_runner.spl`
- `src/os/kernel/arch/riscv64/boot.spl`
- `src/os/kernel/arch/riscv64/interrupt.spl`

However, there is still no checked-in OS-side assembly/vector integration path
already used by the RV64 kernel. That means the missing vector is not just a
small code patch; it also needs a clear build/link path.

### The current kernel bootstrap is still partial

The RV64 boot code is still mostly:
- boot argument capture
- hardcoded QEMU virt memory-map modeling
- early serial logging

It is not yet a full kernel runtime bootstrap that composes scheduler, IPC,
memory, interrupts, and userspace launch into one execution path.

### The current proof lane is unit-level, not end-to-end

The current tests prove the contracts are internally coherent, but they do not
yet prove:
- user-mode entry
- real trap entry
- real trap return
- end-to-end QEMU user syscall execution

That gap is exactly what the missing vector prevents.

## Recommended Next Step

The next implementation slice should be strictly:

1. add a linked RV64 `_rv64_trap_vector`
2. save/restore the `Riscv64Context` trap frame using the offsets in
   `src/os/kernel/arch/riscv64/trap_frame.spl`
3. call `rv64_dispatch_trap_frame_ptr(...)`
4. restore the updated frame
5. return with `sret`
6. add one QEMU proof where an ELF-backed user task executes `ecall` and exits

Do not split attention to Linux, simulator, RV32 parity, or RTL/VHDL before
that is complete.
