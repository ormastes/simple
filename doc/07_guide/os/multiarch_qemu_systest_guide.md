# Multiarch QEMU Systest — Build & Run Guide

SimpleOS has **7 fs-exec systest lanes**: 6 bare-metal QEMU kernels + 1 hosted
macOS process lane. This guide shows how to build, boot, and classify each, plus
the per-lane caveats discovered 2026-06-14.

## Lanes & status (full sweep 2026-06-14, fresh direct boots)

| Lane | qemu | Status | Caveat |
|------|------|--------|--------|
| riscv32 | qemu-system-riscv32 | ✅ GREEN | **build only with the LLVM-backed driver** (cranelift blocks rv32) |
| arm64 | qemu-system-aarch64 | ✅ GREEN | genuine EL0 execution + syscall round-trip |
| arm32 | qemu-system-arm | ✅ GREEN | loader-device boot (no `-kernel`) |
| x86_32 | qemu-system-i386 | ✅ GREEN | `-initrd` FAT32, Limine/multiboot |
| x86_64 | qemu-system-x86_64 | ✅ GREEN | **NVMe + FAT32** block device (not `-initrd`) |
| riscv64 | qemu-system-riscv64 | ❌ RED | rebuild boots OpenSBI then dies silent on **both** backends; good artifact lost — bug `riscv64_cranelift_smf_fs_boot_regression_2026-06-14` |
| aarch64-darwin | none (native process) | hosted — RED on Linux (`missing-media`), GREEN on Apple Silicon | no QEMU; HOSTED_* markers |

## Source of truth

All lane parameters (kernel path, qemu bin, qemu args, markers, timeout) live in
`src/os/qemu_systest_contract.spl`. The build matrix (entry, linker, output, boot
sources per platform) is `src/os/port/simpleos_multiplatform_build_part2.spl`.
Per-lane specs: `test/03_system/os/qemu/sys_qemu_<arch>_fs_exec_spec.spl`.

## Build a kernel

```bash
unset SIMPLE_ALLOW_FREESTANDING_STUBS
env SIMPLE_BOOT_MINIMAL=1 src/compiler_rust/target/debug/simple native-build \
  --source build/os/generated --source src/os --source examples/09_embedded/simple_os \
  --backend <cranelift|llvm> --opt-level=aggressive --entry-closure \
  --entry examples/09_embedded/simple_os/arch/<arch>/<entry>.spl \
  --target <triple> -o build/os/<output>.elf \
  --linker-script examples/09_embedded/simple_os/arch/<arch>/<linker>.ld
```

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

## Known reproducibility caveats

- **riscv64**: rebuild regressed (both backends); only the now-lost Jun-8 86 KB ELF
  booted. Restoration = bisect/debug the riscv64 kernel boot after OpenSBI handoff.
- **arm64**: rebuild blocked in some envs (x86 kernel modules pulled into arm64
  source scope); the committed Jun-13 ELF boots green. Linker dedup statically
  verified equivalent so the lane is safe.
- **riscv32**: not buildable with the default cranelift driver — use LLVM.

## De-duplication

Shared boot/runtime code lives in `examples/09_embedded/simple_os/arch/common/`:
`riscv_common.h`, `linker_riscv_common.ld`, `linker_arm_common.ld` (PL011 serial
header was already shared). See
`doc/05_design/os/multiarch_qemu_systest/duplication_analysis.md`. When deduping a
lane that cannot be rebuilt, verify the refactor **statically**: linker
INCLUDE-expansion must equal the original directive set; a C boot-stub extraction's
normalized translation-unit diff must show only header guards + forward declarations.
