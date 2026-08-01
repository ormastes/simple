# Native Entry-Closure Common Import Type Loss

**Status:** OPEN

## Symptom

A stable-input pure-Simple Stage3 candidate passes sanity but is not
provenance-admitted and cannot build the `simpleos_gpu_host` entry closure.
While lowering
`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`, the import loader resolves
`common.ui.draw_ir` relative to the consumer directory, degrades
`Simple2dDrawIrPlan` to `ANY`, then rejects `plan.batch_id`:

```text
Failed to load imported types from ["common", "ui", "draw_ir"]:
cannot resolve import: module path segment `common` not found
Unsupported feature: cannot infer field type while lowering
_engine2d_draw_ir_result_from_plan: struct 'ANY' field 'batch_id'
```

The defining module exists at `src/lib/common/ui/draw_ir.spl`, and the helper
parameter is explicitly typed as `Simple2dDrawIrPlan`.

## Evidence

- Build-start revision: `47a8b7ec7dd5e146fe2d8220da9c21559b56b8a8`
- Build-end revision: `bf7fb5e00c7a7c3a3ceafd79c61d234c594d6f81`
- Stage3 SHA-256:
  `c2a638a51df632e27352543a458289e857c16bfefd79e020bcce39c608f6870a`
- Stage3 sanity: pass
- Source-input manifests match before and after the build, but the revision and
  dirty fingerprint changed, so canonical provenance is not admitted.
- The retained daemon logs prove the relative-path diagnostic, `ANY` field
  failure, and empty native module-name collision. They do not retain the
  attempted command variants.

Retained logs:

- `build/simpleos_gpu_host/device_warm_wire/daemon-stage3-current-build.log`
- `build/simpleos_gpu_host/device_warm_wire/daemon-stage3-current-build-cycle2.log`
- `build/simpleos_gpu_host/device_warm_wire/daemon-stage3-current-build-cycle3.log`

## Required Repair

Trace why the entry-closure import type loader exhausts its existing project
library and admitted-root fallbacks after the relative lookup fails. Separately
preserve non-empty, distinct module names for explicit source files. Add a
native entry-closure regression using an imported struct field, produce an
admitted compiler, then rebuild the daemon incrementally and run
`device-warm-production`.
