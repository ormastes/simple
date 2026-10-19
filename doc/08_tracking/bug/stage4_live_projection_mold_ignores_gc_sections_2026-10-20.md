# Stage 4 live-request projection is linker-dependent: mold ignores `--gc-sections` under `-r`

- **Date:** 2026-10-20
- **Status:** open; worked around with `SIMPLE_LINKER=lld` on the Phase 4 full-CLI link
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
