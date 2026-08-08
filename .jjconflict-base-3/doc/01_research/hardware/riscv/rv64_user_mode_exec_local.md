<!-- codex-research -->
# RV64 User-Mode Exec — Domain Research

**Feature:** `rv64_user_mode_exec`  
**Date:** 2026-04-02  
**Status:** Draft

## Sources

- RISC-V privileged architecture specification: `https://riscv.github.io/riscv-isa-manual/snapshot/privileged/`
- RISC-V ELF psABI specification: `https://riscv-non-isa.github.io/riscv-elf-psabi-doc/`
- Linux RISC-V boot requirements: `https://docs.kernel.org/arch/riscv/boot.html`

## Findings

### 1. RV64 user return semantics are not optional

The privileged specification makes the blocker explicit:

- `sret` returns according to supervisor status state, not according to the software task type alone
- `SPP=0` means return to U-mode
- `SPP=1` means return to S-mode
- `SPIE` controls whether interrupts are enabled after `sret`
- `sepc` is the architectural return PC and must be advanced after `ecall`

Impact on the repo plan:
- a scheduler-only `is_user` flag is insufficient
- the restored RV64 context must carry correct `sstatus` and `sepc`
- the real trap vector must restore a frame and exit with `sret`, not a generic function return
- the first stable runtime contract should treat the trap frame, not the generic scheduler context, as the architectural source of truth for post-trap resume
- the implementation needs an explicit handoff boundary between:
  - architecture-owned trap-frame save/restore
  - kernel-owned trap classification and syscall dispatch

### 2. RV64 syscall ABI should follow the RISC-V calling convention shape already modeled in the repo

The psABI confirms the standard integer calling convention:

- syscall/call arguments live in `a0` through `a5`
- the call ID lives in `a7`
- the return value comes back in `a0`
- this same register shape is the cleanest contract for the trap-frame adapter and the first proof binary

Impact on the repo plan:
- the current pure trap model shape is correct as the stable contract
- the real trap vector and dispatcher must preserve exactly that register mapping
- unknown syscall numbers and unsupported trap causes should fail explicitly rather than degrade silently
- the first proof binary only needs to exercise one output syscall and `Exit`; Linux ABI breadth is not required here

### 3. Linux boot depends on machine and handoff correctness, not just code generation

The Linux RISC-V boot documentation confirms the key downstream constraints:

- the kernel expects a valid hardware description handoff, typically a DTB
- the kernel image placement and alignment rules matter
- the boot contract includes memory map assumptions and firmware/loader responsibilities
- the conventional Linux handoff also uses `a0` for hart ID and `a1` for the DTB pointer
- for later Linux work, the current `simple-rv64` machine profile must evolve into a machine contract that can also describe DTB, memory layout, and boot handoff details

Impact on the repo plan:
- RV64 Linux boot should remain downstream of the current blocker
- a repo-native simulator will need a stable board/machine contract, not just a CPU execution loop
- the same machine profile used for baremetal OS work should become the basis for Linux boot later
- the blocker docs should name Linux and simulator work as explicit downstream dependencies, not silent future ideas

### 4. The current blocker should stay narrower than Linux or simulator completion

The external specs show that the next credible proof threshold is:

- one real RV64 ELF-backed user task
- correct U-mode entry
- correct `ecall` trap handling
- correct return and exit path

Only after that are the following worth treating as implementation milestones:

- RV32 user-mode parity
- RV64 Linux boot in a repo-native simulator
- full repo-native simulator with device and board model
- generated RTL/VHDL CPU/SoC lanes
- GUI OS running on the repo-native simulator

## Recommended Constraint Set

### Current blocker milestone

- static RV64 ELF exec only
- `spawn_binary(path, priority)` remains the only public launch ABI
- one minimal userspace proof binary is sufficient for the first end-to-end runtime milestone
- `_rv64_trap_vector` should be implemented as the narrowest viable trap entry that handles user `ecall`, timer interrupt, and external interrupt before any broader exception subsystem refactor

### Deferred but explicitly linked downstream milestones

- RV32 user-mode carryover
- VFS-backed executable loading instead of boot-packaged bytes
- Linux boot handoff with machine-profile-derived board contract
- repo-native simulator with device model
- generated RTL/VHDL lanes and GUI OS execution

## Conclusion

External specifications support a narrow and defensible next milestone:

- finish true RV64 user-mode exec first
- keep Linux, repo-native simulation, RTL/VHDL, and GUI OS as named downstream dependencies in the same documentation package
- do not collapse those later milestones into the current acceptance bar
