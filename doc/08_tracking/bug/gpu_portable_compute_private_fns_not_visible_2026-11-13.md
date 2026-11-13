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
