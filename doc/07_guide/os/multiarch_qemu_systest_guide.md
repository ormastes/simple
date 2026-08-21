# Multiarch QEMU Systest — Build & Run Guide

SimpleOS has **7 fs-exec systest lanes**: 6 bare-metal QEMU kernels + 1 hosted
macOS process lane. This guide shows how to build, boot, and classify each, plus
the per-lane caveats discovered 2026-06-14.

## Historical lanes (2026-06-14 direct-boot diagnostics)

The table below is historical diagnostic evidence. It predates the current
Stage-4 compiler, immutable bundle, real-firmware, and mounted-program
admission profile and therefore does not establish a current release PASS.

| Lane | qemu | Status | Caveat |
|------|------|--------|--------|
| riscv32 | qemu-system-riscv32 | ✅ GREEN | LLVM backend **auto-selected** for rv32 by the driver (cranelift blocks rv32) |
| arm64 | qemu-system-aarch64 | ✅ GREEN | genuine EL0 execution + syscall round-trip |
| arm32 | qemu-system-arm | ✅ GREEN | loader-device boot (no `-kernel`) |
| x86_32 | qemu-system-i386 | ✅ GREEN | `-initrd` FAT32, Limine/multiboot |
| x86_64 | qemu-system-x86_64 | ✅ GREEN | **NVMe + FAT32** block device (not `-initrd`) |
| riscv64 | qemu-system-riscv64 | ✅ GREEN | source-reproducible (fixed 2026-06-14); accidental `freestanding_runtime.c` boot wrapper pulled the 100 KB networking runtime into the minimal kernel — renamed → `full_networking_runtime.c` |
| aarch64-darwin | none (native process) | hosted — RED on Linux (`missing-media`), GREEN on Apple Silicon | no QEMU; HOSTED_* markers |

## Source of truth

All lane parameters (kernel path, qemu bin, qemu args, markers, timeout) live in
`src/os/qemu_systest_contract.spl`. The build matrix (entry, linker, output, boot
sources per platform) is `src/os/port/_SimpleosMultiplatformBuild/platform_target_catalog.spl`.
Per-lane specs: `test/03_system/os/qemu/sys_qemu_<arch>_fs_exec_spec.spl`.

## Build a kernel

```bash
SIMPLE_BIN=/absolute/path/to/admitted/stage4/simple
SIMPLE_QEMU_RUNTIME_RECEIPT=/absolute/path/to/stage4.sosix-admission.env \
  sh scripts/check/check-sosix-qemu-runtime-admission.shs \
  --verify "$SIMPLE_BIN" "$SIMPLE_QEMU_RUNTIME_RECEIPT"
unset SIMPLE_ALLOW_FREESTANDING_STUBS
env SIMPLE_BOOT_MINIMAL=1 SIMPLE_NO_STUB_FALLBACK=1 "$SIMPLE_BIN" native-build \
  --source build/os/generated --source src/os --source examples/09_embedded/simple_os \
  --backend <cranelift|llvm> --opt-level=aggressive --entry-closure \
  --entry examples/09_embedded/simple_os/arch/<arch>/<entry>.spl \
  --target <triple> -o build/os/<output>.elf \
  --linker-script examples/09_embedded/simple_os/arch/<arch>/<linker>.ld
```

The selected compiler must be a regular non-symlink file whose exact path,
SHA-256, version, and pure-Simple Stage-4 provenance match the receipt. The
Rust seed and `src/compiler_rust/target/**/simple` are bootstrap-only and never
produce QEMU acceptance evidence.

- **riscv32 requires the LLVM driver** (cranelift refuses rv32):
  `cd src/compiler_rust && LLVM_SYS_180_PREFIX=/usr/lib/llvm-18 cargo build --package driver --features llvm`
- Judge unresolved symbols by `nm <objects-kept>/*.o`, not link success (weak no-op
  defsyms are injected unconditionally).
- Builds get killed under heavy machine load — run nice'd/background with retries.

## Run the full sweep

The specs boot the **existing** ELF (they do not rebuild). The harness test runner
may cache results, so for a true fresh sweep boot each lane directly with its
`<arch>_qemu_args()` from the contract, writing serial to
`build/os/systest/<arch>.serial.log`, then classify.

**Classification gotcha:** host `grep` is aliased to `ugrep`, which **skips matches
in NUL-containing (binary) files** — riscv serial logs contain NULs. Always use
`grep -a` (text mode) for marker checks, or you get false-RED.

```bash
for m in <markers>; do grep -aqF "$m" build/os/systest/<arch>.serial.log && echo ok || echo MISS; done
```

A missing kernel/image classifies as `missing-media:<path>` — a diagnosed RED
failure, never `skip()`.

## Strict x86_64/AArch64/RV64GC release profile

The three-architecture release adapter is:

```sh
sh scripts/check/check-simpleos-three-arch-qemu-bundle.shs --check x86_64 BUNDLE_DIR
sh scripts/check/check-simpleos-three-arch-qemu-bundle.shs --check arm64 BUNDLE_DIR
sh scripts/check/check-simpleos-three-arch-qemu-bundle.shs --check riscv64 BUNDLE_DIR
```

It consumes the canonical SOSIX immutable bundle rather than creating a second
receipt. x86_64 and AArch64 require hash-bound UEFI pflash firmware; RV64GC
requires hash-bound OpenSBI. All rows require target ELF/ABI checks, retained
Stage-4 compiler bytes and source-bound admission, image and mounted-program
hashes, exact argv, ordered serial markers, exit 37/reap, and exactly one
terminal `TEST PASSED`. `-kernel`, `-device loader`, `-bios default`, symlinked
compiler material, source scans, or historical logs fail the profile.

The current adapter is deliberately non-authorizing: caller-authored receipts
and logs plus path-based hashes cannot establish trust. It reports structural
diagnostics, then returns BLOCKED/nonzero until a canonical signed-campaign
authority verifies descriptor-bound no-follow identity and hashes. Do not
interpret `valid-untrusted` as a live result.

Current blockers and exact resume commands are maintained in
`doc/08_tracking/todo/simpleos_three_arch_qemu_execution_evidence_2026-08-20.md`.

## Known reproducibility caveats

- **riscv64**: ✅ source-reproducible (fixed 2026-06-14). The regression was an
  accidental `arch/riscv64/boot/freestanding_runtime.c` whose sole content was an
  `#include` of the full ~100 KB networking runtime. The linker auto-globs every
  `.c` in the entry's `boot/` dir and the `SIMPLE_BOOT_MINIMAL=1` allowlist matched
  its stem, so it was compiled into the minimal kernel (78 KB → 175 KB, displaced
  the `0x80200000` reset vector, silent death after OpenSBI). Fixed by renaming it
  → `full_networking_runtime.c` (out of the minimal allowlist; `ssh_live` still
  gets it). Verified: fresh 78 KB build, real OpenSBI boot, 6/6 markers. bug
  `riscv64_cranelift_smf_fs_boot_regression_2026-06-14` (closed).
- **arm64**: ✅ source-reproducible (fixed 2026-06-14). `arch/arm64/boot/glass_render.c`
  was a symlink to the **x86_64** 157 KB GUI file, pulled in by the boot-dir glob.
  Deleted; rebuilds green from source with no flag. The identical x86 symlink in
  `arch/riscv64/boot/` was also removed.
- **riscv32**: builds with the LLVM backend, now **auto-selected** for rv32 targets
  by the driver (cranelift has no rv32 codegen) — no manual `--backend llvm` needed.
- **Root-cause class — now gated (2026-06-14).** The compiler's `linker.rs`
  auto-globs every `.c`/`.S` in the entry's `boot/` dir, so a stray wrapper or a
  cross-arch symlink is silently compiled in (both bugs above). Instead of
  rewriting the core glob (the per-lane manifests weren't complete, so that would
  break every lane), the existing native-surface verifier is now a **fail-closed
  gate**: `scripts/check-simpleos-native-surface.shs` runs `native_surface_policy_verify`
  (which now also catches symlinks) from the pre-commit hook whenever boot/runtime/
  manifest files change. Any boot source not declared in a lane's
  `boot_c_sources` / `boot_asm_sources` / `grandfathered_native_sources` fails the
  commit. Run it manually: `sh scripts/check-simpleos-native-surface.shs`.

## De-duplication

Shared boot/runtime code lives in `examples/09_embedded/simple_os/arch/common/`:
`riscv_common.h`, `linker_riscv_common.ld`, `linker_arm_common.ld` (PL011 serial
header was already shared). See
`doc/05_design/os/multiarch_qemu_systest/duplication_analysis.md`. When deduping a
lane that cannot be rebuilt, verify the refactor **statically**: linker
INCLUDE-expansion must equal the original directive set; a C boot-stub extraction's
normalized translation-unit diff must show only header guards + forward declarations.
