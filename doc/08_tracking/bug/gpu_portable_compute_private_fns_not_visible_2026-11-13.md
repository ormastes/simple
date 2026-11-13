# gpu_portable_compute public API rejected by the private-import gate (2026-11-13)

- **Severity:** P3
- **Status:** fixed (verification on the seed below)
- **Owner file:** `src/compiler/70.backend/backend/gpu_portable_compute.spl`
- **Related:** `interp_private_names_leak_across_modules_2026-11-05` (the gate that surfaced it)

## Symptom

On `origin/release/1.0.0` @ `ca00f5494ef`, the spec
`test/03_system/app/browser/feature/browser_webgpu_chrome_compute_evidence_spec.spl`
ran 0 of 2:

```
semantic: ...browser_webgpu_chrome_compute_evidence_spec.spl:44:9: function `emit_portable_u32_add_kernel` not found
semantic: ...browser_webgpu_chrome_compute_evidence_spec.spl:83:9: function `emit_portable_2d_optimization_module` not found
```

The JIT demotion line in the same log names the real cause:

```
private fn `emit_portable_u32_add_kernel` of module `compiler.backend.gpu_portable_compute`
(.../gpu_portable_compute.spl) is not visible to test/03_system/.../browser_webgpu_chrome_compute_evidence_spec.spl;
mark it `pub` or `export` it
```

## Root cause

This was **not** a rename, move, or stale-snapshot rewind. `git log -S` shows
both functions are still defined, under the same names, in
`gpu_portable_compute.spl` (lines 511 and 937), and the file has not changed
since `ae55a746719`.

The module declares every function as a bare `fn`, which is private, and it has
no `pub`/`export` of its own. Re-exports in `backend/__init__.spl` do not cover
a braced `use compiler.backend.gpu_portable_compute.{...}` that names the leaf
module directly. The seed's private-import gate (`6e4e4da3fb2`, 2026-11-07, and
`6d15331f91e`, 2026-11-09; `check_private_use_names` in
`src/compiler_rust/compiler/src/interpreter_module/module_loader.rs`) now makes
such a cross-directory import a hard error unless the pair is in
`scripts/check/private_import_baseline.txt`. No pair for this module is
baselined, so every importer outside `src/compiler/70.backend/backend/` broke.
That includes `test/01_unit/compiler/codegen/gpu_portable_compute_spec.spl`,
which ran 0 of 34, and `src/app/portable_compute_emit/main.spl`.

## Fix

The owner module now marks `pub fn` on exactly the 23 functions that are
imported from outside its directory. The set was computed by scanning every
braced `use compiler.backend.gpu_portable_compute.{...}` in `src/`, `test/` and
`scripts/`. No baseline entries were added, and no spec or assertion was
changed.

## Verification (seed `seed-whileval`, one run at a time, MemoryMax=16G)

| spec | before | after |
|---|---|---|
| browser_webgpu_chrome_compute_evidence_spec | 0/2 (ERROR) | 2/2 (host-unavailable branch) |
| browser_webgpu_chrome_draw_evidence_spec | 2/2 | 2/2 |
| webgpu_js_wasm_simple_spec | 127/127 | 127/127 |
| 01_unit chrome_webgpu_compute_evidence_spec | 13/13 | 13/13 |
| 01_unit chrome_webgpu_draw_evidence_spec | 9/9 | 9/9 |
| 01_unit gpu_portable_compute_spec | 0/34 | 29/34 |

## Still open

- **Real Chrome readback is BLOCKED on this host.** Both compute examples now
  pass the real kernel-source assertions. They then take the explicit
  `host-unavailable:electron-missing` branch, because this host has no
  Electron/Chrome. A real WebGPU readback has not been observed here.
- `gpu_portable_compute_spec` keeps 5 failures. Before this fix they were
  hidden by the import error. They are separate content-drift defects, not
  visibility defects:
  - the font atlas composite source (CUDA and Vulkan GLSL) differs from the
    frozen text (3 examples);
  - `nvcc` invocation lacks `--entry fill_u32`;
  - the smoke matrix has 5 entries, not 4.

  Filed as `gpu_portable_compute_spec_content_drift_5_reds_2026-11-13` (P3, open).

## Resolution: `gpu_portable_compute_spec_content_drift_5_reds_2026-11-13` (fixed 2026-11-13)

All 5 reds were **stale spec expectations**. The emitter did not regress, and
no `src/` file changed. Most of the drift came from two test-tree rewrites:

- `88aac2ffe28` is the release/1.0 transplant. It rolled the spec back to an
  older main-side copy and undid several assertions the release line had
  already updated.
- `f1509b5947e` is the `test/unit` -> `test/01_unit` consolidation. It appended
  a stale legacy example and a duplicate `use` line.

Verdict for each failing example:

| example | verdict | evidence |
|---|---|---|
| shared font atlas composite entry (CUDA, Metal needles) | spec stale | `f119f8b7120` made the CUDA source the HIP source minus the HIP include, so it carries the signed form `si < 0 \|\| si >= atlas_count`. The same commit gave Metal a `0xffffffffu / p.quad_height` overflow guard plus a `quad_count` local. Both changes are equivalent or stricter. The spec now also pins `cuda.source == font_atlas_composite_cuda_source()`. |
| Vulkan GLSL font atlas source | spec stale | `63687490087` (perf(vulkan): pack atlas text dispatches) made the production shader the packed multi-glyph one. The single-glyph shader was renamed `font_atlas_composite_vulkan_legacy_glsl_source()`. The old needles now target the legacy function. The packed source is pinned by sha256 `8a5c5422...4444`, the same pin `backend_vulkan_font_spec` and the embedded SPIR-V header carry, and by its packed-ABI needles. |
| nvcc toolchain invocation (`--entry fill_u32`) | spec stale, not a regression | `e2edf611653` deliberately dropped `--device-c --entry`, because nvcc has no `--entry` option and the symbol is verified from the artifact instead (`doc/07_guide/lib/shared_multilingual_gpu_fonts.md`). That commit also changed the spec to an exact `to_equal`, which `88aac2ffe28` rewound. The exact equality is restored. |
| 2D backend plan from a tagged request | spec stale | The emitter adds a font atlas companion artifact per target, so 4 artifacts for `cuda,opencl`. `88aac2ffe28` rewound the indices to a 2-artifact layout while keeping `len == 4`. The pre-transplant block is restored: indices 0-3, companion suffixes, `artifacts=4`. |
| smoke matrix has 4 entries | stale duplicate | `f1509b5947e` appended the legacy 4-entry example. The in-tree 5-entry example (CUDA/HIP/OpenCL/Metal/WebGPU) is a strict superset of it, so the duplicate and the duplicate `use` were deleted. |

The fix also restores assertions that `88aac2ffe28` dropped: the
`artifact_identity` checks and the `.wgsl` suffix on the WebGPU metadata row.

Red to green on the seed, run under a 16G cgroup:

| spec | before | after |
|---|---|---|
| 01_unit gpu_portable_compute_spec | 29/34 | 33/33 (the stale duplicate was removed) |
| 01_unit chrome_webgpu_compute_evidence_spec | 13/13 | 13/13 |
| 01_unit chrome_webgpu_draw_evidence_spec | 9/9 | 9/9 |
| browser_webgpu_chrome_compute_evidence_spec | 2/2 | 2/2 |

Not fixed here: `test/03_system/app/simple_2d/feature/gpu_font_emission_spec.spl:216-220`
still expects the 13-field Vulkan ABI from the packed production source, the
same `63687490087` drift. It was not run in this lane.

Also flagged by review and not fixed here: the packed Vulkan shader has no
u32 overflow guards. It computes `count=qw*qh`, `aw*ah != ac` and
`si=(ay+ly)*aw+ax+lx` and casts `int(p.words[..])` without them, because it
relies on the host packer in `backend_vulkan_font.spl` for bounds. This has
been the case since `63687490087`. Confirming the packer bounds belongs to the
Vulkan font lane.
