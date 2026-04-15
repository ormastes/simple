# RV64 User-Mode Exec Status Report — 2026-04-02

## Summary

This report captures the current state of the `rv64_user_mode_exec` milestone
after the implementation session on 2026-04-02. The primary blocker — a missing
`_rv64_trap_vector` assembly implementation — has been **resolved**. The full
user-mode execution path from ELF loading through U-mode entry, ecall trap,
syscall dispatch, and sret return is now structurally complete.

Previous status: trap policy and runtime bridge existed, but no assembly vector.
Current status: **all layers implemented**, pending QEMU end-to-end verification.

## What Was Implemented (2026-04-02)

### 1. RV64 S-mode trap vector assembly

**Created:** `src/os/kernel/arch/riscv64/trap_vector.S`

Implements two global symbols in `.text.trap`:

- **`_rv64_trap_vector`** — S-mode trap entry/exit (~120 instructions)
  - Swaps sp/sscratch to get kernel stack on U-mode traps
  - Detects S-mode reentrant traps (sscratch == 0 after swap)
  - Saves all 31 GPRs + sepc, sstatus, scause into 272-byte trap frame
  - Calls `rv64_dispatch_trap_frame_ptr(frame_ptr)` — the existing Simple dispatcher
  - Restores CSRs and GPRs from (possibly updated) frame
  - Checks sstatus.SPP to decide sscratch handling on return
  - Returns via `sret`

- **`_rv64_enter_user`** — first U-mode entry from scheduler
  - Accepts Riscv64Context pointer in a0
  - Sets sepc, sstatus from context; sets sscratch = kernel sp
  - Loads all GPRs from context
  - Executes `sret` with SPP=0 to enter U-mode

### 2. Real proof binary with ecall instructions

**Modified:** `src/os/kernel/loader/executable_source.spl`

The `_minimal_rv64_exec()` function now emits 8 real RV64 instructions (32 bytes)
instead of a single NOP:

1. `li a7, 60; li a0, 0x50; ecall` — debug_write('P')
2. `li a7, 4; ecall` — getpid
3. `li a7, 0; li a0, 0; ecall` — exit(0)

ELF program header segment sizes updated from 4 to 32 bytes.

### 3. Multi-architecture debug_write syscall

**Modified:** `src/os/kernel/ipc/syscall.spl`

`_handle_debug_write` is now architecture-specific via `@cfg`:
- `@cfg(riscv64)` / `@cfg(riscv32)` — UART MMIO write to 0x10000000
- `@cfg(x86_64)` / `@cfg(x86)` — COM1 port I/O at 0x3F8
- `@cfg(arm64)` / `@cfg(arm32)` — PL011 UART MMIO at 0x09000000

### 4. Boot integration (sscratch + trap runtime)

**Modified:** `examples/simple_os/arch/riscv64/boot/crt0.S`
- Added `csrw sscratch, _stack_top` after BSS zeroing, before `call spl_start`

**Modified:** `examples/simple_os/arch/riscv64/entry.spl`
- Full kernel bootstrap: UART init, interrupt controller init, scheduler/IPC/klog
  creation, trap runtime installation, proof binary loading, user task spawn,
  and `_rv64_enter_user()` call to enter U-mode

### 5. User-mode entry path

**Modified:** `src/os/kernel/arch/riscv64/context.spl`
- Added `extern fn _rv64_enter_user(ctx_addr: u64)` declaration

**Modified:** `src/os/kernel/scheduler/scheduler.spl`
- Added `get_user_context(task_id) -> Riscv64Context?` method

### 6. QEMU end-to-end test spec

**Created:** `test/qemu/os/usermode/rv64_user_exec_qemu_spec.spl`

Six test cases verifying:
- Trap vector installation
- Trap runtime installation
- User task spawn from proof binary
- U-mode entry at correct entry point
- Serial output from debug_write ecall
- Boot sequence completes after user task

## Updated Proof Matrix

| Area | State |
|------|-------|
| ELF validation + process image | **done** |
| Path-based launch ABI (`spawn_binary`) | **done** |
| Trap model (classify, marshalling, result apply) | **done** |
| Interrupt dispatch (`rv64_dispatch_trap_frame_ptr`) | **done** |
| Syscall dispatch (40+ handlers) | **done** |
| User context creation (SPP=0, SPIE=1) | **done** |
| Trap frame layout (34 fields, 272 bytes) | **done** |
| `_rv64_trap_vector` assembly | **done** (new) |
| `_rv64_enter_user` assembly | **done** (new) |
| Proof binary (debug_write + getpid + exit) | **done** (new) |
| RV64 UART-based debug_write | **done** (new) |
| Boot sscratch setup | **done** (new) |
| Full kernel bootstrap in entry.spl | **done** (new) |
| QEMU e2e test spec | **done** (new) |
| Proven U-mode entry via sret | **pending QEMU verification** |
| User address space (Sv39 page tables) | deferred (initial proof uses identity mapping) |

## Web Research Summary

### RISC-V Privileged Specification (riscv.github.io)

Key architectural constraints verified against the implementation:
- `sret` returns according to `sstatus.SPP`: SPP=0 → U-mode, SPP=1 → S-mode
- `sstatus.SPIE` controls interrupt enable after `sret`
- `sepc` must be advanced by 4 after `ecall` (implemented in `rv64_apply_syscall_result`)
- The trap vector must be aligned to 4 bytes (implemented via `.balign 4`)

### RISC-V ELF psABI (riscv-non-isa.github.io)

Syscall register convention confirmed:
- `a7` = syscall ID, `a0`-`a5` = arguments, `a0` = return value
- This matches the existing `rv64_syscall_args_from_context()` mapping

### sscratch Protocol (common in xv6-riscv, Linux RISC-V)

The sscratch swap protocol used in the trap vector follows the standard pattern:
- sscratch holds kernel sp while in U-mode
- On trap entry, `csrrw sp, sscratch, sp` atomically swaps
- After swap from U-mode: sp = kernel sp, sscratch = user sp
- After swap from S-mode: sp = 0 (detected and fixed up), sscratch = S-mode sp
- sscratch = 0 while in S-mode signals reentrant trap detection

### Linux RISC-V Boot (docs.kernel.org)

Linux boot dependencies noted for future work:
- DTB handoff via a1 register
- Machine contract for memory layout, board model
- These remain downstream of the current user-mode exec milestone

## Architecture Decisions

### sscratch management

The sscratch register is touched in exactly two places:
1. `crt0.S` — set to `_stack_top` at boot
2. `trap_vector.S` — swapped on entry, restored on exit

No other kernel code modifies sscratch, preventing corruption.

### S-mode reentrant trap handling

If a trap occurs while already in S-mode (e.g., timer interrupt during syscall
handling), sscratch is 0. The trap vector detects this case:
- After `csrrw sp, sscratch, sp`, sp == 0 means S-mode reentry
- Recovery: `csrr sp, sscratch` retrieves the original S-mode sp

### Proof binary placement

The proof binary is embedded directly in `executable_source.spl` as hand-encoded
RV64 instructions. This avoids a build-system dependency on a cross-assembler
for the initial proof. Future work can replace this with a real compiled binary.

### Identity-mapped initial proof

The initial proof does not set up Sv39 user page tables. The proof binary
executes at 0x400000, which falls within the kernel's identity-mapped RAM region.
Full user address space isolation with per-task Sv39 tables is deferred to the
next milestone.

## Files Changed

### Created
- `src/os/kernel/arch/riscv64/trap_vector.S` — trap entry/exit assembly
- `test/qemu/os/usermode/rv64_user_exec_qemu_spec.spl` — e2e QEMU test

### Modified
- `src/os/kernel/loader/executable_source.spl` — real proof binary instructions
- `src/os/kernel/ipc/syscall.spl` — multi-arch debug_write
- `examples/simple_os/arch/riscv64/boot/crt0.S` — sscratch setup
- `examples/simple_os/arch/riscv64/entry.spl` — full kernel bootstrap
- `src/os/kernel/arch/riscv64/context.spl` — _rv64_enter_user extern
- `src/os/kernel/scheduler/scheduler.spl` — get_user_context method

## Downstream Dependency Map

```
rv64_user_mode_exec (this milestone — structurally complete)
 ├── RV32 user-mode carryover
 ├── VFS-backed executable loading
 ├── Sv39 per-task user address space
 ├── RV64 Linux boot
 │    └── repo-native simulator with board/device contract
 │         └── GUI OS on simulator
 └── generated RV32/RV64 RTL/VHDL end-state
```

## Verification Plan

1. `riscv64-unknown-elf-as trap_vector.S` — verify assembly encoding
2. `simple os build --arch=riscv64` — no undefined symbols for `_rv64_trap_vector`
3. `simple os run --arch=riscv64` — boots, installs stvec, prints trap runtime messages
4. QEMU serial output contains 'P' from user debug_write ecall
5. QEMU serial output shows clean task exit
6. `simple os test --arch=riscv64` — all boot + usermode tests pass

## Recommended Next Steps

1. **QEMU verification** — run the kernel under `qemu-system-riscv64` and verify
   the serial output matches the test expectations
2. **Sv39 user address space** — allocate per-task page tables so user code runs
   in isolated virtual memory instead of identity-mapped kernel space
3. **RV32 carryover** — replicate the trap vector and runtime model on RV32
4. **VFS-backed exec** — replace boot-packaged bytes with filesystem loading
5. **Do not** start Linux boot, simulator, or RTL/VHDL work until steps 1-2 are
   verified
