# rv32 native-build: silent 255 FIXED; freestanding runtime completed

**Date:** 2026-06-30
**Area:** compiler / native-build (LLVM backend, `riscv32-unknown-none`) + freestanding RISC-V runtime
**Status:** RESOLVED.

## Symptom (original)

`bin/simple native-build --backend llvm --target riscv32-unknown-none ...` exited **255 with no
diagnostic and no ELF**, for any entry.

## Root cause + fix (resolved)

Two coupled toolchain defects, both fixed and **on origin** (ancestors of `main`):

1. **Mis-route to a too-slow interpreted worker (silent 255).** `native-build` is in
   `command_is_pure_simple_tool`, so the dispatcher ran the `.spl` worker, which eagerly loads the
   whole compiler+LLVM import graph in the interpreter. With a large `--source` set it exceeds the
   timeout budget → coreutils `timeout` (124) → `process_ops` remaps to `-1` → `exit(-1)` = 255.
   - **Fix A (pure Simple, `a0652371728`):** `native_build_main.spl` prints an explicit,
     non-truncatable line distinguishing the timeout sentinel and naming the cause/knobs.
   - **Fix B (Rust seed, `187c62110138`):** route `native-build` to the in-process Rust
     `handle_native_build` when an explicit `--target` is passed (host builds stay pure-Simple).
     It parses `--target`/`--linker-script`, defaults rv32 to LLVM, threads the target into
     codegen, and links via `ld.lld`.

**Deploy:** the OS build resolves `src/compiler_rust/target/release/simple` for any llvm build
(`_find_simple_binary_for_target`), so cross-target builds use the fixed seed directly. Cross-target
is a seed-only capability (the self-hosted AOT hardcodes the host target), so the shared self-hosted
`bin/simple` is intentionally **not** overwritten.

## The "runtime gap" was diagnosed against the wrong build

The earlier note here claimed `rt_native_eq`/`rt_native_neq`/`rt_riscv_uart_put` were missing. That
came from building the **standalone** `fw_rv32/entry.spl`, whose parent dir has no `boot/` — so
native-build's `entry.parent()/boot` C autodiscovery linked nothing. Those symbols are in fact
provided by the shared freestanding runtime
(`src/os/kernel/arch/riscv64/boot/freestanding_runtime.c`, `#include`d by the rv32 bridge
`src/os/kernel/arch/riscv32/boot/baremetal_stubs.c`), which **is** autodiscovered when the entry is
`src/os/kernel/arch/riscv32/boot.spl`.

## The real gap: three missing freestanding primitives (FIXED)

Building the rv32 kernel the correct way (`--entry src/os/kernel/arch/riscv32/boot.spl`, sources
`build/os/generated src examples`) reduced the undefined set to exactly three runtime primitives the
compiler emits but the shared freestanding runtime did not define: `rt_string_char_at`,
`rt_value_as_int`, `rt_array_pop`.

- **Fix (`5ac934cd285`):** added the three to `freestanding_runtime.c`, modeled on its tagged-value
  ABI (`rt_int`/`rt_index_arg`/`rt_as_string`/`rt_as_array`, nil on OOB). Marked `weak` because the
  riscv64 lane also links the per-arch `examples/.../riscv64/boot/baremetal_stubs.c`, which already
  provides strong `rt_array_pop`/`rt_string_char_at`; weak lets the arch strong def win where present
  and supplies the impl for lanes (rv32 boot.spl) that link only this runtime.
- **`boot_main`** is not a runtime symbol; it is rooted by the full-`src`/`examples`/`generated`
  closure the canonical OS build uses (the narrow `src/os`+`src/lib` set prunes it because the only
  reference is inside `_start`'s inline-asm string).

## Verified

- `native-build --target riscv32-unknown-none` compiles riscv objects and links (no silent 255).
- The rv32 **fs-exec** ELF (`build/os/simpleos_riscv32_smf_fs.elf`) builds fresh (exit 0, via the
  fixed seed) **and boots** under `qemu-system-riscv32 -bios none`: prints
  `=== SimpleOS RV32 smoke boot === / SimpleOS RV32 boot OK` (the trailing `TEST FAILED` is only the
  absent fat32 disk image, not a boot failure).
- The rv32 **boot.spl kernel** (`build/os/simpleos_riscv32.elf`) links with **0 undefined runtime
  symbols** using the completed freestanding runtime. Its reset vector at `0x80000000` correctly
  trampolines (`j` → `…riscv32__boot___start`) into boot.spl's real `_start`.

## Not in scope (no longer claimed as a blocker)

A full-OS boot.spl kernel built with the deliberately over-broad `--source src` closure (≈274 KB vs
the canonical lane's ≈106 KB) did not print a banner in a quick QEMU run. The reset trampoline is
correct, so this is an artifact of the over-broad closure pulling extra modules, not an entry-layout
bug and not related to the runtime change. Reproduce on the canonical smoke lane before treating it
as a defect.
