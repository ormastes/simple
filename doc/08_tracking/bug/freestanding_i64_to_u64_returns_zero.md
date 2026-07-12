# BUG: `.to_u64()` on a local `val PAGE: i64` returns 0 in freestanding native-build (cranelift, x86_64-unknown-none)

**Status:** open — worked around at the one known call site; needs a root codegen fix + regression
**Severity:** high (silent wrong value from a primitive int conversion; corrupted a page-mapping loop and a heap size, taking down in-guest clang)
**Component:** native-build codegen — `i64.to_u64()` lowering in freestanding/`--target x86_64-unknown-none` builds
**Found:** 2026-07-12 (in-guest clang heap lane, isolated with serial diagnostics)

## Symptom

In `src/os/kernel/loader/x86_64_fs_exec_ring3.spl`, the map_heap block had:

```
val PAGE: i64 = 4096                 # function-local (declared earlier at ~line 354/95)
...
vmm_zero_phys_range(hph, PAGE.to_u64())
... HEAP_VA + (hp * PAGE.to_u64()) ...
rt_user_heap_init(HEAP_VA, HEAP_PAGES * PAGE.to_u64())
```

Serial diagnostics printed: `HEAP_PAGES=16384 page_u64=0 product=0`. So `PAGE.to_u64()`
evaluated to **0** even though `PAGE` is `4096`. Consequences:
- the page-mapping loop mapped all 16384 pages to `HEAP_VA + 0` (same VA) — only 4 KB
  really backed;
- the user heap size became `16384 * 0 = 0`, so `rt_user_heap_init` set end==base;
- clang's first `mmap` in ring-3 returned ENOMEM → libc `abort()` → exit 134.

Replacing `PAGE.to_u64()` with a fresh `val HEAP_PAGE_SZ: u64 = 4096` fixed both (heap
truly 64 MiB backed) and clang then ran to `clang version 20.0.0git` + clean exit(0).

## Scope / notes

- This is the same freestanding native-build family as the module-val / boxing landmines
  already documented for this file (the header comment notes structured fields "read
  garbage under freestanding native-build"). `.to_u64()` on a local i64 val is another
  such miscompile.
- A plain `u64` literal/`val` works; the miscompile is specifically the `i64 -> u64`
  method conversion in this context.
- The same `PAGE.to_u64()` appeared to "work" in the mapping loop only because a zero
  stride still let 16384 map calls succeed (all overwriting one VA) without a FAIL — a
  silent wrong result, not a crash.

## Repro direction

Minimal: a freestanding `--target x86_64-unknown-none` native-build with a function-local
`val x: i64 = 4096`, print `x.to_u64()` to serial; expect 4096, observe 0. Compare against
a `val y: u64 = 4096` (correct). Then fix the i64->u64 conversion lowering and add the
regression. Until then the workaround (fresh u64 constant) is in place at the sole call site.
