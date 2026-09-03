# `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` has never compiled

**Filed** 2026-09-01 · **Status** partly addressed · **Severity** high

## Symptom
The file is 3,537 lines with ~240 `rt_*`/`spl_*` definitions -- including the
only VirtIO-GPU display bring-up for riscv64 in the tree -- and it does not
compile at all:

    clang --target=riscv64-unknown-none-elf -ffreestanding -fsyntax-only \
      src/os/kernel/arch/riscv64/boot/freestanding_runtime.c
    -> fatal error: too many errors emitted, stopping now (20 errors)

## Why nothing noticed
`native-build` derives its boot directory as `<entry>.parent()/boot`
(`native_project/linker.rs:2033`). The only entry under
`src/os/kernel/arch/riscv64/` is `user_entry.spl`, so essentially no lane
compiles this file, and boot-source compile failures are reported as a
**WARNING**, not an error: "N boot source file(s) failed to compile; resulting
ELF may have undefined refs". A never-compiled file is indistinguishable from a
working one under that policy. Same defect class as the `RtCoreUInt` incident
recorded in `.claude/rules/vcs.md`.

## Two defects found inside it
* `rt_display_flush_test()` calls `rt_gpu_fill_test_pattern()`, which is defined
  **nowhere in the tree**. Zero callers, so it was dropped rather than given an
  invented body.
* `rt_put_le32` / `rt_put_le64` / `rt_get_le32` are declared **twice** (extern at
  the top, `static` again later -- itself a conflict) and defined nowhere.

## Addressed
The PCI + virtqueue + VirtIO-GPU + display portion is extracted into
`src/os/kernel/arch/riscv64/boot/rv64_display_backend.inc.c`, which compiles
clean and is `#include`d by a real TU in the boot dir that lanes actually link
(`examples/09_embedded/simple_os/arch/riscv64/boot/rv64_display_backend.c`). The
two defects above are fixed in the extracted copy.

## Still open
The remaining ~2,700 lines of `freestanding_runtime.c` (boot TCP/SSH, storage,
networking, sandbox) are still uncompilable and unreached by any lane. Either
fix them or delete them -- as of this record nobody can tell which of those 240
symbols are real. A tree-scoped compile guard over `src/os/kernel/**/boot/*.c`,
in the style of `check-c-runtime-compiles-push.shs`, would prevent a recurrence.
