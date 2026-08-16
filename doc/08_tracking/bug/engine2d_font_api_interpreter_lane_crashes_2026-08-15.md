# Engine2D font/backends APIs crash under the interpreter lane (5 distinct sites)

**Date:** 2026-08-15
**Status:** RESOLVED (2026-08-15; re-verified on the current seed 2026-08-16)
**Severity:** P2 — `bin/simple test` hard-defaults to the interpreter, so no
spec can exercise these APIs until fixed; JIT (`bin/simple run` default) is
unaffected (all sites verified working there).

All repros: `SIMPLE_EXECUTION_MODE=interpreter bin/simple run <probe>` on a
`Engine2D.create_with_backend(32, 32, "cpu")` instance (Rust seed, 2026-08-15).

| # | Call | Interpreter error |
|---|---|---|
| 1 | `Engine2D.create_with_backend(8, 8, "cuda")` | `invalid assignment: cannot assign field on non-object value` (every other name incl. vulkan/metal/rocm resolves; vulkan resolves to a REAL device here) |
| 2 | `select_font_identity("no-such")` then any `draw_text` | select returns false, next draw_text: `undefined field: unknown property or method 'width' on Option` |
| 3 | `draw_text_with_advances(...)` (valid args) | `'width' on Option` |
| 4 | `draw_text_points_dpi(...)` | `'width' on Option` |
| 5 | `load_font("/no/such.ttf")` | `invalid assignment: nested field access not fully supported` |

Plain `draw_text` (non-empty and empty), primitives, read_pixels,
`font_receipt_identity_matches`, `cancel_vulkan_present_source` all work.
Sites 2-4 smell like one root cause: an Option-typed font-owner field read
via `.width` without unwrap on the interpreter path; site 5 is the known
interpreter nested-field-assignment limitation; site 1 is a field assign on
a nil CUDA FFI object.

Discovered while extending
test/01_unit/lib/gpu/engine2d/draw_ir_adv_branch_coverage_spec.spl, which
now restricts itself to the working surface and references this doc.
Related lane-divergence context:
doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md.

## RESOLVED 2026-08-15 (same day)

All five sites fixed and verified:

- Sites 2-4 root cause: the interpreter lane does not narrow an Option-typed
  binding for FIELD access after `!= nil` (method calls dispatch by name and
  worked, masking it). Fixed with explicit `.unwrap()` rebinds at the three
  glyph/advance cache hits in
  `src/lib/nogc_sync_mut/text_layout/font_renderer.spl`.
- Site 5 root cause: `self.font_owner.active[0] = fonts` nested assignment
  (unsupported on the interpreter). Fixed via new `_install_active_fonts()`
  local-rebind helper in `src/lib/gc_async_mut/gpu/engine2d/engine.spl`
  (39 call sites replaced).
- Site 1 (cuda create) was the same font-path defects reached through
  `install_pinned_cuda_font_artifact` — resolved by the fixes above; cuda now
  resolves under the interpreter (real device present).
- Additional harness-only crash found while verifying: `FontRasterizer.load()`
  read a missing unmanaged font via the COLLIDING `file_read_bytes` duplicate
  (returns nil, not [], under the co-compiled test harness) then called
  `.len()` on it. Fixed fail-closed with a `file_exists` guard in
  `src/lib/nogc_sync_mut/sffi/spl_fonts.spl`.

Evidence: interpreter probes green for all five repros;
`bin/simple test test/01_unit/lib/gpu/engine2d/draw_ir_adv_branch_coverage_spec.spl`
(cuda re-enabled, full font lanes restored): `Results: 13 total, 13 passed,
0 failed`; engine.spl decision coverage 3% -> 19%.

## Re-verified 2026-08-16 (current seed, origin/main fd085136a6d)

The seed's nested + augmented ClassInstance field-assignment support (landed
2026-08-15/16) is in; re-ran
`bin/simple test test/01_unit/lib/gpu/engine2d/draw_ir_adv_branch_coverage_spec.spl`
(interpreter-default test lane): `Results: 13 total, 13 passed, 0 failed`.
Bitmap/vector font offload, font_runtime_config, engine_vulkan_font_route,
font scalar receipt, and font offload preference smoke specs also green (see
the bungee bug doc's fix, same session).
