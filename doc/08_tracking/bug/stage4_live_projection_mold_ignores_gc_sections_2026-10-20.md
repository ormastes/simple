# Stage 4 live-request projection is linker-dependent: mold ignores `--gc-sections` under `-r`

- **Date:** 2026-10-20
- **Status:** fixed 2026-10-20 (`work/phase4-link-mold-simple`): the Linux projection is computed in-process; no linker runs
- **Where:** `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs` `stage4_live_runtime_requests` (~:901-975)
- **Seen on:** seed `51d63d3f…` (cranelift), authorized Stage 4 entry `src/app/cli/main.spl`, tree `a41a729c5fd`, host linker default resolving to `mold` (`~/.local/bin/mold`)

## Symptom

After a clean 2792-unit compile the exact Stage 4 profile aborts with

```
Build failed: Stage4 requested symbols have no archive owner: rt_alloc_page_aligned,
rt_arm64_dcache_clean_range, ... (113 symbols: winit 10, oneapi 10, intel 10, http 8,
arm 8, port 7, webgpu 6, mmio 6, engine2d 5, ws 4, metal 4, virtio 3, cuda 3, ...)
```

Every one of the 113 is dead code in the CLI closure (baremetal, provider DSO stubs, unbacked
externs already in `unbacked_extern_baseline.txt`).

## Root cause

`stage4_live_runtime_requests` computes the live runtime demand with a relocatable link
`-Wl,-r -Wl,--gc-sections -Wl,-u,main -Wl,-u,spl_main` and honours `SIMPLE_LINKER` /
the C driver's default linker. mold accepts `--gc-sections` together with `-r` but does not
perform section GC in that mode, so the projection's undefined set is the whole pre-GC set.
Measured on the same 2792 objects:

| linker | undefined after `-r --gc-sections` | of the 113 dead symbols |
|---|---|---|
| lld  | 784  | 0 |
| mold | 1578 | 113 |

The final hosted link then never runs: the profile refuses before it because the "live"
request list contains symbols no provider owns.

## Workaround

`SIMPLE_LINKER=lld` for the Stage 4 build (same objects, zero recompile).

## Fix wanted

The projection must not depend on the host's default linker: force `-fuse-ld=lld` for the
`-r` projection when `ld.lld` is available, or fail closed when the projection's undefined
set is not smaller than the objects' union of undefined symbols (no GC happened), naming the
linker. A mold-only host should get a clear error, not 113 false "no archive owner" rows.

## Resolution (2026-10-20)

GNU ld.bfd 2.x behaves like mold here: measured on the same 2793-input projection set,
`-r --gc-sections` leaves 775 `rt_`/`spl_` undefined under lld and 1564 under both mold and
bfd. Forcing lld would only have moved the dependency, so the Linux projection no longer runs
a linker at all. `src/compiler_rust/compiler/src/pipeline/native_project/live_projection.rs`
walks the objects' section/relocation graph the way LLD's mark phase does. Roots are
`main`/`spl_main` plus the always-kept sections. `.eh_frame` and non-ALLOC sections never
mark anything. Strong definitions beat weak ones and the first COMDAT group wins. The pass
fails closed on any object it cannot parse. The macOS `-dead_strip` trial link is unchanged.

Evidence, using the kept Phase 4 objects (`native-objects-1G3YX9`, 2793 inputs) and the
ignored test `live_projection::tests::matches_lld_projection_of_real_object_set`:

- The in-process set equals lld's full `nm -u` set of the `-r --gc-sections` output:
  782 symbols, 0 extra and 0 missing. Of those, 775 are `rt_`/`spl_`.
- It runs in ~1.0-2.4 s in a debug build. lld's `-r` projection takes 1.54 s.

With the projection fixed, the final link of those objects under mold succeeds:

- `readelf -d` NEEDED is libm, libgcc_s and libc (no sqlite).
- `--version` and `-c 'print(1+1)'` print `2`.
- `nm -D -u` shows 0 `rt_`/`spl_` symbols, and no dynamic relocation names one.
- Plain `nm -u` lists 577 `rt_`/`spl_` UND entries. These are `.symtab`-only: mold keeps
  undefined symbols from GC'd sections in the static symbol table, and lld drops them.
  Acceptance under mold therefore has to check `nm -D -u`.
