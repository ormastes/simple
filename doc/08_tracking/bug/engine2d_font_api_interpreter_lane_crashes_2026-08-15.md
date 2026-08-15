# Engine2D font/backends APIs crash under the interpreter lane (5 distinct sites)

**Date:** 2026-08-15
**Status:** OPEN
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
