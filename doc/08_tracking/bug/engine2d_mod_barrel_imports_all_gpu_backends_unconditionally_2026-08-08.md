# SimpleOS baremetal kernel link drags in CUDA/Metal host-GPU FFI — root cause is `engine.spl`'s `Engine2D` facade, NOT `mod.spl`

**Filed:** 2026-08-08
**Severity:** high — blocks the SimpleOS desktop-kernel freestanding link /
QEMU-boot evidence gate (`scripts/check/check-simpleos-wm-fullscreen-evidence.shs`)
at exactly 6 unbaselined symbols: `rt_cuda_memset_d32`,
`rt_metal_device_identity`, `rt_metal_device_supports_metal3`,
`rt_metal_load_library_bytes`, `rt_metal_load_library_bytes_raw`,
`rt_metal_load_library_file`.
**Status:** FIXED (the 6-symbol blocker) — option 2 (device-absent bodies)
landed 2026-08-08 in `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`.
All 6 symbols confirmed gone from the freestanding-link fabricated-stub list
via a re-run of `check-simpleos-wm-fullscreen-evidence.shs`
(SIMPLE_BIN pinned to stage2). The gate still fails overall, but now on a
DIFFERENT, unrelated, out-of-scope symbol (`rt_file_is_char_device`) that
comes from uncommitted WIP elsewhere in the shared working copy, not from
this fix or from `origin/main`. See
`doc/09_report/os/simpleos_2d_render_qemu_evidence_2026-08-07.md`
("2026-08-08: option 2 landed" section) for the full verification trace.

## Corrected root cause (traced via `nm -u`/`nm` on real build objects, not inference)

The prior report
(`doc/09_report/os/simpleos_2d_render_qemu_evidence_2026-08-07.md`, "7 of 13
fabricated-stub symbols implemented" section) attributed the remaining 6
symbols to `src/lib/gc_async_mut/gpu/engine2d/mod.spl` lines 108-121 (the
package barrel's unconditional `use` of every backend). **That attribution
is wrong.** Verified from the actual failed-run build artifacts still on
disk (`build/simpleos_wm_fullscreen_evidence2/native-objects-K0fOB0/`, 774
objects):

```
$ nm *.o | grep -E "engine2d__mod__|engine2d__engine__|CudaBackend|MetalBackend"
mod_158.o / mod_160.o / mod_171.o / mod_219.o / mod_220.o / mod_261.o /
mod_262.o / mod_492.o / mod_497.o / mod_498.o:
    U lib__gc_async_mut__gpu__engine2d__engine__Engine2D
mod_183.o: V lib__gc_async_mut__gpu__engine2d__backend_cuda__CudaBackend
mod_194.o: V lib__gc_async_mut__gpu__engine2d__backend_metal__MetalBackend
mod_223.o: U lib__gc_async_mut__gpu__engine2d__backend_cuda__CudaBackend
```

**No object in the closure contains any `engine2d__mod__` symbol at all** —
the `mod.spl` barrel is not part of this compiled closure. What every
consuming object actually references is `engine2d__engine__Engine2D` — the
`Engine2D` facade class defined in
`src/lib/gc_async_mut/gpu/engine2d/engine.spl`.

Source-level confirmation of the import chain the kernel build actually
takes (bypassing `mod.spl` entirely):

- `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl:44` →
  `use os.compositor.compositor_engine2d.{Engine2dCompositorBackend}`
- `src/os/compositor/compositor_engine2d.spl:1` →
  `use std.gpu.engine2d.engine.{Engine2D}`
- `src/os/compositor/engine2d_display.spl:17-18` → same: imports
  `engine.{Engine2D}` and `backend_baremetal.{BaremetalBackend}` directly —
  it already bypasses the barrel, which is the *correct* pattern the kernel
  side uses everywhere else.
- `src/lib/gc_async_mut/gpu/engine2d/engine.spl:38,52` unconditionally
  imports `backend_cuda.{CudaBackend}` and `backend_metal.{MetalBackend}`,
  and — critically — **declares them as struct fields on `Engine2D`
  itself**:
  ```
  cuda_backend: CudaBackend? = nil     # engine.spl:230
  metal_backend: MetalBackend? = nil   # engine.spl:234
  ```
  with six call sites constructing/using them inside ordinary (non-`@cfg`)
  method bodies (`engine.spl:435,533,552,611,770,812`), e.g.
  `var metal = MetalBackend.create()` and `var cuda = CudaBackend.create()`
  inside methods that are always compiled as part of the `Engine2D` type,
  regardless of which backend a given call site runtime-selects.

## Why this is NOT an import-gating problem (and a `mod.spl` edit would be a no-op)

Even a perfect target-conditional `use` mechanism applied to `mod.spl`
would leave the 6 symbols exactly where they are, because:

1. `mod.spl` isn't in the compiled closure for this entry — confirmed above.
2. The actual culprit type, `Engine2D`, is a single monolithic class used
   identically by every consumer (macOS Metal apps, CUDA apps, and this
   baremetal kernel). `cuda_backend`/`metal_backend` are **fields on that
   one struct**, not conditionally-imported free functions — gating a `use`
   statement cannot remove a struct field or the methods that reference it.
   The class itself would need to be *split*: a lean `Engine2D` variant
   (baremetal/software backends only) for `compositor_engine2d.spl` /
   `engine2d_display.spl`, versus the full facade for hosted builds. That
   is a genuine cross-cutting API-surface refactor, not a target-predicate
   fix.

## Conditional-compilation mechanism check (why STOP, not hack)

Searched for an existing mechanism the codebase already uses to gate
imports/struct fields by target (freestanding/baremetal vs hosted):

- `@cfg(x86_64)` / `@cfg(arm64)` / `@cfg(riscv64)` exists (407 uses,
  `scripts/check/cert/redeploy_gate/fixtures/cfg_*.spl`) but is strictly an
  **arch-dispatch mechanism for selecting between multiple same-named
  top-level function bodies** — not a predicate for
  freestanding-vs-hosted, not applicable to `use` statements, and not
  applicable to struct field declarations.
- No `@cfg(baremetal)`, `@cfg(freestanding)`, `@cfg(nostdlib)` or
  equivalent token found anywhere in the tree
  (`git grep -n "@cfg(" -- '*.spl'` — every hit is an arch token).
- No other target-conditional-import or target-conditional-field mechanism
  found in `src/compiler/**`.

Per this task's explicit instruction not to hack `mod.spl` in a way that
risks breaking host consumers, and given the fix site turned out to require
splitting a shared class's struct layout (which a `use`-level gate cannot
do even if one existed), **no source change was made this pass**.

## What an actual fix requires (for whoever picks this up)

One of:
1. **Split the facade**: introduce a lean `Engine2D` (or a
   `BaremetalEngine2D`) without `cuda_backend`/`metal_backend` fields and
   the 6 call sites, used by `compositor_engine2d.spl` /
   `engine2d_display.spl` only; keep the full `Engine2D` unchanged for
   every other consumer. Requires auditing `compositor_engine2d.spl`'s
   actual usage surface of `Engine2D` to confirm the lean type's subset API
   suffices.
2. **Real freestanding bodies** for the 6 `rt_metal_*`/`rt_cuda_memset_d32`
   symbols that correctly report "no Metal/CUDA device present" on this
   target (categorically different from the `rt_push`-returns-0 style
   fabricated stub the gate rejects — a real "device absent" answer is
   semantically correct for a baremetal-framebuffer x86_64 kernel that will
   never have a Metal or CUDA device). This sidesteps the facade-split
   entirely but adds 6 small freestanding C/asm shims to
   `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`
   (the file already holds the sibling `rt_push`/`rt_engine2d_simd_*`
   bodies landed 2026-08-08).
3. A new compiler-level conditional-compilation mechanism generalizing
   `@cfg` to `use` statements and struct fields, scoped by target triple
   class (freestanding vs hosted) rather than just arch — the heavier,
   more general option; out of scope to design here.

Option 2 is likely the smallest safe fix and doesn't touch the shared
`Engine2D` facade at all; option 1 is more architecturally correct but
cross-cutting exactly as the prior report already flagged.

## Verification not re-run this pass

No source was changed, so the 900s
`check-simpleos-wm-fullscreen-evidence.shs` gate and the host-side engine2d
regression spec were not re-run — both would reproduce the already-recorded
6-symbol failure with no new information. Next session picking up option 1
or 2 above should re-run the gate after the fix; expected ladder: 6 symbols
gone from the unbaselined set → freestanding link passes → QEMU (OVMF
pflash) launches → serial output.

## Files referenced

- `src/lib/gc_async_mut/gpu/engine2d/engine.spl` (lines 38, 52, 230, 234,
  435, 533, 552, 611, 770, 812) — actual fields/call sites
- `src/lib/gc_async_mut/gpu/engine2d/mod.spl` (lines 108-121) — NOT in this
  closure; leave as-is
- `src/os/compositor/compositor_engine2d.spl`, `src/os/compositor/engine2d_display.spl`
  — kernel-side consumers of `Engine2D`
- `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl` — entry
  point that pulls the chain in
- `doc/09_report/os/simpleos_2d_render_qemu_evidence_2026-08-07.md` — prior
  report with the (corrected-here) `mod.spl` attribution
- `build/simpleos_wm_fullscreen_evidence2/native-objects-K0fOB0/` — the
  traced build objects (local scratch, not committed)
