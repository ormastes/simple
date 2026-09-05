# HIR lowering: "cannot infer field type" is the only signal for an undeclared struct field (no file:line to the real defect)

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).

- **Date:** 2026-08-08
- **Severity:** P2 (blocks native build of any closure that reaches the affected struct; misleading diagnostic hides the real defect)
- **Repro (before fix):** `SIMPLE_BIN=build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs` (native-build step)
- **Error:**
  ```
  hir: Unsupported feature: cannot infer field type while lowering
  SimpleWebEngine2DStaticPixelCache.retain_result_for_html: struct
  'SimpleWebLayoutEngine2DReadbackResult' field 'resolved_backend'
  hir: Unsupported feature: cannot infer field type while lowering
  _web_render_label_backend: struct 'SimpleWebLayoutEngine2DReadbackResult'
  field 'resolved_backend'
  ```

## Details

The reported "cannot infer field type" diagnostic pointed at two *consumer*
sites (`SimpleWebEngine2DStaticPixelCache.retain_result_for_html` in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl:152`
and `_web_render_label_backend` in
`src/lib/gc_async_mut/ui/web_render_pixel_backend.spl:322`), but neither of
those files is where the real defect lives. The actual root cause:

`class SimpleWebLayoutEngine2DReadbackResult` is declared in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl:80-96`.
Commit `ca75bf0700a` ("label an artifact with the backend that produced its
pixels", 2026-08-05) added `.resolved_backend` reads/writes in
`simple_web_engine2d_renderer.spl` and `web_render_pixel_backend.spl`, and
added `resolved_backend:` to the ONE constructor call in
`simple_web_engine2d_renderer.spl:179` — but never added the field to the
class declaration itself, and never added `resolved_backend:` to the other
THREE constructor call sites of the same struct
(`simple_web_layout_engine2d_fast.spl:727, 743, 763`).

So the struct had a field that was: read by two consumers, set by exactly one
of four constructors, and declared nowhere. The frontend/type-checker did not
reject this as an undeclared-field / missing-required-field error at the
construction or declaration sites — it was silently accepted, and the failure
surfaced only much later, in HIR lowering, as a generic "cannot infer field
type" message that names a *consumer* function and the struct/field, but
gives no file:line for the class declaration or for the constructors that
omit the field. A developer chasing the reported error has to manually find
all four constructor sites and the class declaration; nothing in the
diagnostic points there.

## Expected

One of:
1. A missing/inconsistent field across a struct's declaration and its
   constructor call sites should be a hard parse/type-check error at the
   declaration or construction site (e.g. "constructor for X is missing
   required field `resolved_backend`" or "field `resolved_backend` used at
   line N is not declared on struct X"), not a downstream HIR inference
   failure.
2. If HIR lowering is where this is first detected, the diagnostic should
   include the struct's declaration file:line so the fix location is
   immediately obvious, not just the struct name and the unrelated
   consumer function that happened to trigger lowering.

## Workaround applied (source-only, no compiler change)

Added `resolved_backend: text` to the class declaration and
`resolved_backend: backend_name` to the three previously-incomplete
constructors in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl`.
See `doc/09_report/os/simpleos_2d_render_qemu_evidence_2026-08-07.md` ("Fix +
re-run" section) for the verification run.

## Owner

Compiler/HIR-lowering + type-checking maintainer, `src/compiler/**`. Filed
per repo rule: a safe source-level workaround must not silently normalize a
real gap in the compiler's frontend validation.
