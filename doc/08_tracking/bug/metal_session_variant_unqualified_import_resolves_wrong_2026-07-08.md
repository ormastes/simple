# Unqualified `std.gpu.engine2d.metal_session` import can resolve to the wrong memory-model variant

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

**Found:** 2026-07-08, incidental finding during the "new kernel not found"
blocker investigation (`engine2d_metal_new_kernel_pipeline_not_found_2026-07-07.md`).
**Severity:** low — real callers are unaffected (see below); this only bites a
throwaway repro script written outside a variant folder.

## Symptom

The stdlib ships two parallel per-memory-model variants of `metal_session.spl`
with **different method sets**:

| Variant | Path | `MetalSession` init method |
|---------|------|----------------------------|
| gc_async_mut  | `src/lib/gc_async_mut/gpu/engine2d/metal_session.spl`  | `me init() -> bool` |
| nogc_sync_mut | `src/lib/nogc_sync_mut/gpu/engine2d/metal_session.spl` | `me init_device() -> text` (and a `MetalPipelineCache` class) |

A script that imports the **unqualified** path
`use std.gpu.engine2d.metal_session.{MetalSession}` from **outside** either
variant directory can resolve to the `nogc_sync_mut` variant, and then a call
to `session.init()` fails at runtime with `method 'init' not found` (that
variant only offers `init_device()`). Both variants share the same
`static fn create(mode: text) -> MetalSession` constructor, so construction
succeeds and the divergence only surfaces at the first method call.

## Why real callers are unaffected

- `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl` resolves
  `metal_session` **same-directory** (→ the `gc_async_mut` variant with
  `init()`).
- `test/02_integration/rendering/engine2d_gpu_offload_evidence.spl` reaches it
  transitively through `std.gc_async_mut.gpu.engine2d.engine`, i.e. the
  fully-qualified `gc_async_mut` path.

So no production caller hits the wrong variant. This is purely a
resolution gotcha for ad-hoc scripts.

## Workaround

Always import the **fully-qualified** variant path from a standalone script:

```
use std.gc_async_mut.gpu.engine2d.metal_session.{MetalSession}   # has init() -> bool
```

(The step-2a probe `scratchpad/probe_pipe_indexed_fill.spl` does exactly this.)

## Suggested fix (not done here)

Unqualified `std.<...>.metal_session` resolution across memory-model variants
with divergent public method sets should either (a) be a resolution error that
names the ambiguous candidates, or (b) deterministically prefer the variant
matching the importing module's memory-model family. Filed as a record; not
fixed in the GPU-dict pilot change.

## 2026-08-17 update — scope is WIDER than this doc claimed (lane w02/s6a)

Classified by CONTENT (grep of current source), not SHA ancestry.

**`metal_session` itself is clean.** Every real caller already spells the lane:
`src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:13` and
`backend_metal_font.spl:4` both use
`std.gc_async_mut.gpu.engine2d.metal_session`. The only unqualified occurrence
was the *usage doc comment* in `metal_session.spl:12`, which advertised the
ambiguous form to anyone copying it. **Fixed in this change** — that comment now
spells the lane and states the hazard.

**But the "no production caller hits the wrong variant" claim above is true only
for `metal_session`.** A census of the same directory found **19 modules under
`gpu/engine2d/` that exist in BOTH `gc_async_mut/` and `nogc_sync_mut/`**:

    backend_session, cuda_session, ffi_cuda, ffi_dispatch, ffi_intel, ffi_rocm,
    ffi_vulkan, framebuffer_hooks, metal_session, sffi_cuda, sffi_dispatch,
    sffi_intel, sffi_opencl, sffi_rocm, sffi_vulkan, simd_kernels,
    simd_provider, vulkan_session, webgpu_surface

and roughly **20 live `use std.gpu.engine2d.<twin>` import sites in `src/lib`
that do NOT spell a lane**, in production code in both lanes, e.g.:

- `src/lib/gc_async_mut/gpu/engine2d/compute_dispatch.spl:8` — `backend_session`
- `src/lib/gc_async_mut/gpu/engine2d/render_2d_riscv.spl:20,21` — `cuda_session`, `backend_session`
- `src/lib/gc_async_mut/gpu/engine2d/render_2d_x86_session.spl:15,20` — same pair
- `src/lib/gc_async_mut/gpu/engine2d/backend_opencl.spl:11` — `sffi_opencl`
- `src/lib/gc_async_mut/gpu/engine2d/backend_probe.spl:4` — `simd_kernels`
- `src/lib/nogc_sync_mut/gpu/engine2d/{ffi,sffi}_{cuda,intel,rocm,vulkan,opencl}.spl` — `{ffi,sffi}_dispatch`
- `src/lib/nogc_sync_mut/io/vulkan_sffi.spl:6` — `sffi_dispatch`
- `src/lib/nogc_sync_mut/spec/evidence/counterpart/host_vulkan_lavapipe_provider.spl:97` — `sffi_vulkan`

So the ambiguous-resolution surface in shipped stdlib code is ~20 sites, not
zero, and this row's "real callers unaffected / severity low" triage note
understates it. These sites are apparently resolving to the intended lane today
(the code works), which is exactly what makes it dangerous: nothing is an error,
and a resolution-order change would silently rebind them.

**Deliberately NOT blind-patched.** Rewriting 20 imports to qualified paths
without an execution-level check of which variant each currently binds could
itself flip a working site to the other lane — the same silent-wrong-result
failure this row is about. The census is recorded here so the fix can be done
deliberately, one lane at a time, with per-site evidence.

**Not proven by this lane:** which variant each of those ~20 sites actually
binds at runtime. The host had all 6 `test-slot.shs` slots saturated by parallel
sessions for the duration of this work, so no execution evidence was collected;
the findings above are source-content evidence only.

## Triage 2026-08-17 (lane m7c_lib_async) — LIVE, unchanged

Both same-named variants are still present:
`src/lib/gc_async_mut/gpu/engine2d/metal_session.spl` and
`src/lib/nogc_sync_mut/gpu/engine2d/metal_session.spl`. The ambiguity this doc
records therefore still exists. The mis-binding itself is a module-resolver
defect in the compiler, not something a `src/lib/**` edit can fix without
renaming one public module — out of scope for this lane, and the doc's own
severity note (real callers unaffected, all qualify their import) stands.
