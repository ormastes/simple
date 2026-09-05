# Bug: freestanding `rt_pool_safepoint` undefined on non-x86_64 baremetal arches

**ID:** freestanding_rt_pool_safepoint_undefined_2026-06-14
**Status:** FIXED (origin `f47ddc609bd` — scoped to arm64 only; supersedes the intermediate all-arches `8c8128fa815`)
**Severity:** P1 — breaks the arm64 QEMU systest lane from a clean source build (cranelift-emitted symbol; other lanes verified unaffected)
**Found by:** multiarch QEMU systest full-sweep verification (clean-worktree rebuild of every lane)

## Symptom

Building the arm64 fs_exec kernel from committed source (clean worktree, `SIMPLE_ALLOW_FREESTANDING_STUBS` unset) fails at link:

```
ld.lld: error: undefined symbol: rt_pool_safepoint
>>> referenced by simple_module
>>>   mod_1.o:(lib__common__string_core__str_repeat)
>>>   mod_11.o:(lib__nogc_async_mut__fs_driver__fat32_dir_ops__fat32_create_file)
>>> referenced 582 more times
```

No ELF produced → lane is `BLOCKED`, not the GREEN the FINAL STATE table claimed.

## Root cause

The "multicore green" loop-safepoint work injects a call to `rt_pool_safepoint()`
at MIR loop lowering (`mir/lower/lowering_stmt.rs`). The freestanding runtime
provides arch-specific symbol definitions by globbing `arch/<arch>/boot/*.c`.
Only **x86_64**'s `boot/baremetal_stubs.c` defined `rt_pool_safepoint`
(`int64_t rt_pool_safepoint(void){ return 0; }`). The other freestanding arches
(arm64, arm32, riscv64, riscv32, x86_32) never got the stub — an incomplete
rollout when the safepoint runtime was added. Any kernel whose linked code
contains a qualifying loop (here: `str_repeat`, fat32 write ops) references the
symbol and fails to link on those arches.

Why it stayed hidden: the lanes were last "verified" by booting pre-existing
(possibly orphaned) ELFs, not by rebuilding from source. x86_64 has the stub;
riscv64's smf_fs kernel happens not to reference the symbol (its included code
has no qualifying loop), so both passed and masked the gap. A clean-source
rebuild of arm64 (which pulls in the fat32 write path) exposed it.

**Backend finding (from the full sweep):** the symbol is emitted by the
**cranelift** backend at loop lowering. The LLVM-backed lanes (arm32, riscv32,
x86_32 — cranelift has no 32-bit codegen for these) were clean-rebuilt from
committed source and showed **0 unresolved without the stub** — LLVM does not
emit the call. So among the cranelift arches (arm64, riscv64, x86_64), only
arm64's fs_exec kernel actually references it today; the LLVM lanes never do.

## Fix

Add the trivial no-op (single-core baremetal has no thread pool to yield to) to
**arm64**'s `boot/baremetal_stubs.c` — mirroring the one x86_64 already has:

```c
int64_t rt_pool_safepoint(void) { return 0; }
```

**Scope: arm64 only.** The per-arch stub files define runtime symbols on an
as-needed basis (they are deliberately different subsets), so the stub is added
only where a clean-source build actually references it. The full-sweep rebuild
proved every other freestanding lane links clean *without* it:
- arm32 / riscv32 / x86_32 use the **LLVM** backend, which never emits the call
  (0 unresolved, verified by clean rebuilds).
- riscv64 is cranelift but its smf_fs kernel has no qualifying loop (0 unresolved,
  verified). x86_64 already defines it (its fs_exec references it, like arm64's).

So only arm64's fs_exec kernel (fat32 write + str_repeat loops, cranelift) needed
the stub. Adding it elsewhere would be unused code.

## Verification (full clean-rebuild sweep, 2026-06-14)

All 6 QEMU lanes rebuilt from committed source in isolated worktrees / main:
- **arm64**: with the fix → links clean (0 unresolved, 1880 KB ELF,
  `T rt_pool_safepoint`) and **boots GREEN 7/7 markers** incl genuine EL0
  `user-svc-exit:ok`. End-to-end confirmed.
- **riscv64** (cranelift), **x86_64** (cranelift), **arm32** (LLVM),
  **x86_32** (LLVM), **riscv32** (LLVM): all rebuilt clean from source (0
  unresolved) and boot GREEN with their full marker sets — none reference the
  symbol. The LLVM lanes required building an `--features llvm` driver from
  committed Rust source (system LLVM 18.1.8).

## Prevention note

This is the same class of footgun the boot-dir-glob gate
(`scripts/check-simpleos-native-surface.shs`) was added for: a compiler-emitted
symbol whose freestanding definition is provided per-arch and can silently
diverge. Consider a check that every compiler-injected runtime symbol has a
definition in every freestanding arch's stub set.
