# Board-Runnable Rule

**When work is developed against QEMU, it MUST be runnable on the real dev board
too — unless the user explicitly states otherwise.** LLVM/clang and the Simple
compiler targeting SimpleOS specifically must run on the physical board, not just
QEMU.

QEMU is the dev harness; the board is the target. A QEMU-only result is a defect,
not a completion.

## What this requires
- **Real-firmware proxy, always:** boot via OVMF pflash (x86_64), OpenSBI
  (riscv), or EDK2/AAVMF (aarch64) — **never** QEMU `-kernel` pass semantics and
  **never** `isa-debug-exit`. The proxy exists so the same artifact runs on
  hardware. (aarch64 currently lacks an EFI-stub — that gap is filed and is
  exactly the kind of thing this rule forbids leaving implicit.)
- **Board bring-up path kept alive:** every QEMU-developed feature (kernel, LLVM
  toolchain, in-guest binaries, drivers) keeps a documented physical-board build
  + boot + run path. See `doc/03_plan/os/simpleos/hw_qemu/` and
  `doc/03_plan/os/in_guest_clang_selfhost_board_plan.md`.
- **Board evidence bar** for any board claim: board identity + download/boot path
  + serial or SSH transcript — same rigor as the QEMU real-firmware gate.

## When board-run is genuinely blocked
Say so explicitly and file it (missing hardware, a driver gap, an EFI-stub gap).
Do NOT silently ship QEMU-only and imply board-runnable. Scope to QEMU-only only
when the user says so.

See also: `.claude/rules/bootstrap.md` (board-proxy notes),
`.claude/memory/ref_*` and `doc/07_guide/os/simpleos_llvm_toolchain.md`.
