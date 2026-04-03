# OS Build & Boot Crash Report

**Date:** 2026-04-03
**Environment:** macOS arm64 (Darwin 25.3.0), QEMU 9.x, Cranelift backend
**Binary:** `bin/simple` (Rust bootstrap → `src/compiler_rust/target/bootstrap/simple`)

---

## Summary

| Arch | Build | Boot | Root Cause |
|------|-------|------|------------|
| **riscv64** | OK (42.9 MB, 41s) | CRASH | Wrong `_start` symbol (x86 serial test kernel wins) + no asm trampoline |
| **arm64/aarch64** | FAIL (all 3466 files) | N/A | `"aarch64-unknown-none"` triple → `BinaryFormat::Unknown` (missing `-elf`) |
| **x86_64** | Objects OK, link FAIL | N/A | `ld64.lld` (macOS Mach-O) used instead of `ld.lld` (ELF linker) |
| **riscv32** | FAIL (all files) | N/A | Cranelift has no riscv32 backend |
| **arm32** | Not tested | N/A | Same as aarch64 (`"armv7a-unknown-none-eabihf"` may lack `-elf`) |
| **x86_32** | Not tested | N/A | Likely same linker issue as x86_64 |

---

## Detailed Crash Analysis

### 1. RISC-V 64 — Builds but crashes at boot

**Build command:**
```bash
SIMPLE_LIB=$(pwd)/src bin/simple native-build \
  --entry src/os/kernel/arch/riscv64/boot.spl \
  --target riscv64-unknown-none \
  -o build/os/simpleos_riscv64.elf \
  --linker-script src/os/kernel/arch/riscv64/linker.ld --clean
```

**Build result:** SUCCESS — `3466 compiled, 0 cached, 0 failed`

**QEMU command:**
```bash
qemu-system-riscv64 -machine virt -cpu rv64 -m 128M -serial stdio \
  -display none -no-reboot -bios default -kernel build/os/simpleos_riscv64.elf
```

**Observed behavior:**
- OpenSBI v1.7 boots successfully, prints full banner
- OpenSBI configures `Domain0 Next Address: 0x0000000080200000`, `Next Mode: S-mode`
- OpenSBI jumps to `0x80200000`
- **Infinite fault loop**: `fault_fetch` at `epc=0x0000000000000000` (cause=1)

**Root cause chain:**

1. **Wrong `_start` symbol resolution:**
   - ELF entry point: `0x8218605C`
   - `_start` (global) at `0x8218605c` → resolves to `nogc_async_mut_noalloc__baremetal__x86__serial_test_kernel___start`
   - This is an **x86** function, not the RISC-V 64 boot entry!
   - The `--defsym=spl_start=<candidates>` mechanism picks the LAST `_start` across ALL source files, and the x86 serial test kernel wins

2. **OpenSBI ignores ELF entry point:**
   - OpenSBI always jumps to its configured payload address `0x80200000` (start of `.text`)
   - The ELF entry point (`0x8218605C`) is 24 MB into the binary — OpenSBI doesn't use it
   - Code at `0x80200000` is whatever function got linked first — not the kernel entry

3. **No assembly trampoline:**
   - The linker script has `KEEP(*(.text.entry))` for `_start` placement
   - But Simple compiler doesn't emit section-attributed assembly — `.text.entry` is empty
   - Baremetal kernels need a tiny asm stub: set `sp`, call `kernel_main`
   - Without this, the first byte at 0x80200000 is a random function body

4. **The random function at 0x80200000 returns to address 0:**
   - Stack pointer is uninitialized or 0 (OpenSBI doesn't set it for payload)
   - Return instruction reads garbage from stack → jumps to 0x0
   - CPU gets `fault_fetch` at `epc=0x0000000000000000` — infinite trap loop

**RISC-V 64 boot symbols (from ELF):**
```
0x8276ef40 os__kernel__arch__riscv64__boot___save_boot_args
0x8276f188 os__kernel__arch__riscv64__boot___build_memory_map
0x8276ff64 os__kernel__arch__riscv64__boot___build_boot_output
```
These are 24 MB past `.text` start — they should be near the beginning.

**Fix required:**
- [ ] Add arch-specific `_start` asm trampoline for riscv64 (sets `sp`, calls `spl_main` or boot entry)
- [ ] Fix `--defsym` to select only the arch-matching `_start` candidate
- [ ] Or: emit a `.section .text.entry` attribute on the boot entry function
- [ ] Ensure riscv64 boot functions are linked at `.text` start (before all other code)

---

### 2. ARM64/AArch64 — Build fails: binary format unknown

**Build command:**
```bash
SIMPLE_LIB=$(pwd)/src bin/simple native-build \
  --entry src/os/kernel/arch/arm64/boot.spl \
  --target aarch64-unknown-none \
  -o build/os/simpleos_aarch64.elf \
  --linker-script src/os/kernel/arch/arm64/linker.ld --clean
```

**Error:** ALL 3466 files fail with:
```
codegen init: Module error: Backend error: binary format is unknown
```

**Root cause:**

In `src/compiler_rust/common/src/target.rs:519`:
```rust
(TargetArch::Aarch64, TargetOS::None) => "aarch64-unknown-none",
```

The triple `"aarch64-unknown-none"` lacks the `-elf` suffix. When `target_lexicon` parses this, it assigns `BinaryFormat::Unknown`. Cranelift's `ObjectBuilder::new()` rejects unknown binary formats.

Compare with working triples:
```rust
(TargetArch::X86_64, TargetOS::None)  => "x86_64-unknown-none-elf",   // has -elf ✓
(TargetArch::Riscv64, TargetOS::None) => "riscv64gc-unknown-none-elf", // has -elf ✓
(TargetArch::Aarch64, TargetOS::None) => "aarch64-unknown-none",       // missing -elf ✗
(TargetArch::Arm, TargetOS::None)     => "armv7a-unknown-none-eabihf", // possibly OK (eabi implies ELF?)
```

**Fix required:**
- [ ] Change `"aarch64-unknown-none"` → `"aarch64-unknown-none-elf"` in `target.rs:519`

---

### 3. x86_64 — Link fails: wrong linker flavor

**Build command:**
```bash
SIMPLE_LIB=$(pwd)/src bin/simple native-build \
  --entry examples/simple_os/arch/x86_64/entry.spl \
  --target x86_64-unknown-none \
  -o build/os/simpleos_x86_64.elf \
  --linker-script examples/simple_os/arch/x86_64/linker.ld --clean
```

**Compilation:** SUCCESS — objects are `ELF 64-bit LSB relocatable, x86-64` (correct format)

**Link error:**
```
ld64.lld: error: unknown argument '--entry=_entry32'
ld64.lld: error: unknown argument '--defsym=spl_start=...'
ld64.lld: error: unknown argument '-z'
ld64.lld: error: unknown argument '--unresolved-symbols=ignore-all'
ld64.lld: error: unknown argument '-T'
```

**Root cause:**

On macOS, `clang --target=x86_64-unknown-none-elf` still invokes `ld64.lld` (Mach-O linker) instead of `ld.lld` (ELF linker). The ELF-specific flags (`--entry`, `--defsym`, `-T`, `-z`) are rejected by the Mach-O linker.

The linker selection in `native_project.rs` (around line 1504-1580) uses `clang --target=...` to drive linking, but macOS clang defaults to ld64 regardless of the target triple for non-system targets.

**Fix required:**
- [ ] Use `ld.lld` directly for freestanding/baremetal targets (skip clang as linker driver)
- [ ] Or: pass `-fuse-ld=lld` and `-Wl,--target2=rel` to force ELF linker flavor
- [ ] Or: detect macOS and invoke `ld.lld` directly with ELF flags

**Additional issue:** Missing `src/os/kernel/arch/x86_64/linker.ld` — only `examples/simple_os/arch/x86_64/linker.ld` exists. The `qemu_runner.spl` references the wrong path.

---

### 4. RISC-V 32 — Cranelift backend not available

**Error:** ALL files fail with:
```
codegen init: Compilation error: Support for this target has not been implemented yet
```

**Root cause:** Cranelift does not have a riscv32 code generator (only riscv64). The `riscv32gc-unknown-none-elf` triple is valid for target_lexicon but there's no ISA implementation.

**Fix required:**
- [ ] Use LLVM backend for riscv32 (already partially implemented), or
- [ ] Skip riscv32 in the OS test matrix until Cranelift adds riscv32, or
- [ ] Cross-compile riscv32 via C backend + riscv32 gcc cross-compiler

---

### 5. Incremental Cache Contamination

**Observed:** First builds failed because the incremental cache contained Mach-O arm64 (host) objects from a previous host-target build. When `--target riscv64-unknown-none` was specified, the cache served stale host objects.

**Evidence:** Objects in temp dir were `Mach-O 64-bit object arm64` for a riscv64 build — after `--clean`, objects were correct `ELF 64-bit LSB relocatable, UCB RISC-V`.

**Fix required:**
- [ ] Include target triple in cache key to prevent cross-target contamination
- [ ] Or: invalidate cache when target changes

---

## Affected Files

| File | Issue |
|------|-------|
| `src/compiler_rust/common/src/target.rs:519` | Missing `-elf` suffix for aarch64 |
| `src/compiler_rust/compiler/src/pipeline/native_project.rs` (link section) | Wrong linker flavor on macOS for cross targets |
| `src/compiler_rust/compiler/src/pipeline/native_project.rs` (defsym) | Wrong `_start` selected — x86 wins over riscv64 |
| `src/compiler_rust/compiler/src/pipeline/native_project.rs` (cache) | Target not in cache key |
| `src/os/qemu_runner.spl:70` | References missing `src/os/kernel/arch/x86_64/linker.ld` |

---

## Fixes Applied (2026-04-03)

1. **aarch64 `-elf` suffix** — `target.rs:519`: `"aarch64-unknown-none"` → `"aarch64-unknown-none-elf"` ✅
2. **`_start` defsym arch filter** — `native_project.rs`: positive/negative filters by `__riscv__` etc. ✅
3. **macOS cross-linker** — `native_project.rs`: use `ld.lld` directly for freestanding targets on macOS ✅
4. **Startup object ordering** — `native_project.rs`: object containing `_start` is placed first in link ✅
5. **Boot dir assembler fallback** — `native_project.rs`: fall back to Homebrew LLVM clang for cross-assembly ✅
6. **Cache key** — `native_project.rs`: target triple appended to incremental cache path ✅
7. **riscv64 crt0.S** — `src/os/kernel/arch/riscv64/boot/crt0.S`: S-mode trampoline (set sp, zero BSS, call boot_main) ✅
8. **riscv64 boot_main** — `src/os/kernel/arch/riscv64/boot.spl`: boot_main() function for S-mode entry ✅

## Post-Fix Status

| Arch | Build | Boot | Notes |
|------|-------|------|-------|
| **riscv64** | OK | OK (no output) | Boots, enters boot_main, halts cleanly. No serial output because runtime string functions are stubbed. |
| **arm64** | OK | Not tested yet | Needs crt0.S similar to riscv64 |
| **x86_64** | OK | Needs ELF32 | QEMU multiboot needs 32-bit ELF; objcopy step fails |
| **riscv32** | FAIL | N/A | Cranelift has no riscv32 backend |

## Remaining

1. **riscv32** — punt to LLVM or skip in matrix
2. **arm64 crt0** — needs AArch64 boot stub similar to riscv64
3. **x86_64 ELF32** — objcopy/multiboot32 path needs fixing
4. **Serial output** — boot_main needs direct MMIO writes (not runtime string functions)
