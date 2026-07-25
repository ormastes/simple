# Plan: Simple compiler/loader/interpreter on SimpleOS on-board (x86_64/aarch64/riscv64) + CI

Status: ACTIVE 2026-07-13. Goal: the Simple toolchain (interpreter + compiler)
runs as a SimpleOS FS executable, board-proven on all three 64-bit arches, with
Simple CI building the per-arch SimpleOS binaries.

## Where we are (verified 2026-07-13)

- x86_64: `bin/release/x86_64-unknown-simpleos/simple` (3.8MB static ELF, entry
  0x40000000) BUILDS and RUNS on the OVMF board proxy (no `-kernel`): ring-3,
  streams its own ELF from NVMe, reads `/hello.spl` (39B), then FAULTS at
  `cr2=0x8` in `rt_string_join` (nil array in the print path). Serial-proven.
- Bug: `doc/08_tracking/bug/simpleos_freestanding_nil_array_init_optimizer_guard_fold.md`.
- Current build route (updated 2026-07-15): the committed `bin/release/simple`
  launcher selects the pure-Simple self-hosted compiler for
  `native-build --target <triple>`. `SIMPLE_BUILD_COMPILER` remains
  an explicit bootstrap/debug override; architecture wrappers no longer
  select the Rust seed automatically.

## Critical-path bug fix (keystone — all arches share it)

The nil-array fault reproduces on every arch (freestanding one-binary builds
skip module-global array initializers; the seed optimizer folds guards on
`i64`-typed params). Two fixes; do the contained one first:
- **(b) Re-type the runtime string helpers** (`rt_string_join`/`rt_string_*`
  in `src/runtime/simple_core/core_string.spl`) to take `[T]` (or route the
  handle through an `as i64` cast) so the surviving-guard trick applies — the
  optimizer won't fold a guard behind the cast. Contained to core_string.spl.
- **(a) Codegen: run freestanding array-init** so module-global arrays are
  never nil. Cleaner, also fixes the Lane A class; bigger change. Fallback if
  (b) is insufficient.

## Lanes (parallel)

### Lane BX — x86_64 complete (critical path)
1. Apply fix (b) to core_string.spl (+ any sibling rt_string_* the print path
   hits). 2. Rebuild the SimpleOS binary with the selected pure-Simple compiler.
   3. Re-run
   `scripts/os/ssh_simple_hello_uefi.shs` (OVMF, no -kernel) → assert
   `/hello.spl` prints "hello from simple on simpleos" over SSH. 4. Stretch:
   `simple compile --emit-object /hello2.spl -o /hello2.o` in-guest → getfile
   → ET_REL. Save binary + evidence to sweep-immune recover; HOLD source for
   gate.

### Lane BA — aarch64
Cross-build `simpleos_tool` for `aarch64-unknown-simpleos` with the selected
compiler (arm has FS-exec infra: `services/vfs/arm_fs_exec_*`, virtio-blk).
Board gate:
QEMU `-machine virt -cpu cortex-a72` (+ UEFI/EDK2 aarch64 if available, else
the arm boot path the existing arm64 lanes use — NOT a QEMU-only shortcut that
bypasses firmware). Inherit BX's fix once landed; until then, confirm
boot-to-same-fault to prove the loader path works on arm64. readelf: link base
must clear the arm kernel layout.

### Lane BR — riscv64
Same for `riscv64-unknown-simpleos` (riscv has `smf_fs` build stamps + proven
SMP). Board gate: QEMU `-machine virt -cpu rv64` with OpenSBI firmware (real
firmware path, board-representative). Inherit BX's fix.

### Lane CI — Simple CI builds the three SimpleOS binaries
Add a CI entry (Simple-native, e.g. under `src/app/ci/` or a
`scripts/ci/build-simpleos-toolchain.shs`) that, for each of
{x86_64,aarch64,riscv64}-unknown-simpleos, invokes the selected pure-Simple
compiler for `native-build` of
`src/app/simpleos_tool/main.spl`, verifies the artifact (static ELF, correct
link base, no PT_LOAD in the kernel band), writes a build stamp, and publishes
to `bin/release/<triple>/simple`. Gate: all three artifacts produced +
stamped. Wire into the existing CI/check harness. This is the "simple ci build
binary to support simple os" deliverable.

## Cross-arch link bases (must respect per arch)
- x86_64-simpleos: payload/entry 0x40000000 (clear of OVMF kernel .bss
  [0x08000000,0x16400000)).
- aarch64/riscv64: confirm each arch's user link base clears its kernel image;
  record in sysroot.shs per-arch (simpleos.ld generator).

## Rules
- Board-proxy = real firmware (OVMF x86, EDK2/UEFI or arch boot for arm,
  OpenSBI for riscv). No `-kernel` pass semantics on x86; no isa-debug-exit.
- Build with the pure-Simple self-hosted compiler. Use the Rust seed only for
  an explicit bootstrap/debug override, never as an automatic fallback.
- Central-compiler .spl changes: HOLD for the bootstrap gate; land only after
  the parallel redeploy settles. Harness/CI/arch-build scripts land freely.
- Evidence = serial transcript quoted per arch; artifact readelf verified.
- Snapshot every lane's files to sweep-immune scratchpad on report.
