# Bug: freestanding `rt_pool_safepoint` undefined on non-x86_64 baremetal arches

**ID:** freestanding_rt_pool_safepoint_undefined_2026-06-14
**Status:** FIXED (origin `8c8128fa815`)
**Severity:** P1 — breaks the arm64 (and latently the arm32/riscv/x86_32) QEMU systest lanes from a clean source build
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

## Fix

Add the same trivial no-op to each freestanding arch's `boot/baremetal_stubs.c`
(single-core baremetal has no thread pool to yield to):

```c
int64_t rt_pool_safepoint(void) { return 0; }
```

Applied to arm64, arm32, riscv64, riscv32, x86_32 (x86_64 already had it). This
completes the freestanding-runtime ABI surface consistently across all arches.

## Verification

- **arm64**: rebuilt from committed source + the fix → links clean (0 unresolved,
  1880 KB ELF, `T rt_pool_safepoint` defined) and **boots GREEN 7/7 markers**
  including genuine EL0 `user-svc-exit:ok`. End-to-end confirmed.
- arm32/riscv64/riscv32/x86_32: receive the identical trivial no-op
  (`int64_t f(void){return 0;}` — cannot fail to compile). arm32 re-verified
  by rebuild+boot.

## Prevention note

This is the same class of footgun the boot-dir-glob gate
(`scripts/check-simpleos-native-surface.shs`) was added for: a compiler-emitted
symbol whose freestanding definition is provided per-arch and can silently
diverge. Consider a check that every compiler-injected runtime symbol has a
definition in every freestanding arch's stub set.
