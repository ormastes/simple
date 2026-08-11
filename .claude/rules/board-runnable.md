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
  hardware. **aarch64 now has a real-firmware lane** — EDK2/AAVMF pflash ->
  `vendor/limine/BOOTAA64.EFI` (a real EFI application on a FAT ESP) ->
  `kernel.elf`, gated by
  `scripts/check/check-simpleos-arm64-efi-real-firmware-boot.shs`, with its ESP
  built reproducibly by `scripts/os/build-simpleos-aarch64-efi-esp.shs`. (The
  earlier "aarch64 lacks an EFI-stub" wording here was stale: the chosen design
  is an EFI *application* chain, mirroring x86_64's, not a PE/COFF stub on the
  kernel — see that build script's header for why.) **The remaining aarch64 gap
  is a different one and is still filed:**
  `scripts/check/check-simpleos-arm64-unified-live.shs`, the main arm64 desktop
  lane, still boots with QEMU `-kernel` and must be migrated onto the
  real-firmware chain above. The **kernel-side** half of that migration is now
  done: the unified kernel's `crt0.S` carries an arm64 Linux `Image` header plus
  a self-relocation stub, so `BOOTAA64.EFI` can load it with `protocol: linux`
  (MMU-off physical handover — the same contract `-kernel` gave it), gated by
  `scripts/check/check-simpleos-arm64-unified-boot-contract.shs`. The lane edit
  itself waits on a self-hosted `bin/simple` that can build the unified kernel.
  See `doc/08_tracking/bug/arm64_efi_real_firmware_lane_unreproducible_and_unified_lane_uses_kernel_2026-08-11.md`.
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
