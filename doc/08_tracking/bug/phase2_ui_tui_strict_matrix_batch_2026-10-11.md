# Phase-2 strict matrix: UI/TUI/GUI batch root-cause record (2026-10-11)

Lane: work/rel-ui-tui-fixes-20261011 on f92764f2b97. Strict validation via
the admitted stage-2 compiler in the render-harden worktree (read-only);
seed oracle from the release-llvm worktree (read-only).

## Fixed in this batch

### 1. Free-function `len(x)` had no self-hosted lowering (compiler fix)

The seed accepts `len(x)`; the HIR interpreter dispatches it by name
(`interpreter_calls.spl lookup_builtin_tag` has a `case "len"`). The
self-hosted compiler rejected it at TWO layers:

- HIR: `is_interp_builtin_fn` (20.hir/hir_lowering/_Expressions/
  expression_support.spl) omitted "len" -> "unresolved name: len" for every
  module using the free form. The UI/TUI tree uses it heavily
  (34 sites across tui/layout.spl, tui/widget.spl, tui/widgets/*).
- MIR: no intercept for a bare `len(...)` CALL existed in lower_call.

Fix: allow-list "len", and in `lower_call`'s is_direct block re-dispatch as
`MethodCall(receiver=x, "len", [], Unresolved)` so the call reuses the
method arm's receiver-provenanced rt_len / rt_string_len / rt_dict_len
lowering (same pattern as the field-callee re-dispatch at
method_calls_literals.spl). Regression spec:
`test/01_unit/compiler/50.mir/free_len_call_lowering_spec.spl` — FAILs on
the unedited tree (verified by stash control), PASSes with the fix, both
under the seed runner (in-process parse->HIR->MIR, so no bootstrap lane is
needed to keep this covered).

### 2. `common.ui.draw_ir` exported less than its importers need (source fix)

`src/lib/common/ui/draw_ir.spl` declared 80 top-level names but exported
27. The seed tolerates importing non-exported names; strict HIR fails
closed, and every engine2d-dependent UI closure (gui_shell pulls
gc_async_mut/gpu/engine2d) died with "unresolved type: DrawIrRect"
(attribution is misleading — the failing importer is named in the
chase-unresolved receipt, not in the error line). Exported the 40 imported-
but-unexported names as an explicit list (repo style rule: no 'export use *').

### 3. Imported-struct call-result binding loses provenance (house fix x2)

`val report = enforce_mcdc_exact_coverage(...)` then `report.machine_report()`
and `val info = extract_skip_feature_info(f)` then `info.status.lower()`
both fail strict MIR with unresolved method calls, while adding the
explicit type annotation (`val report: McdcCoverageGateReport = ...`,
`val info: SkipFeatureInfo = ...`) fixes them. Minimal repros:
build/ui-probes/p3_exact.spl / p4_bisect.spl / p5_ann.spl (local struct:
works; imported struct via local-fn call result: fails; annotated: works).
Fixed at src/compiler/80.driver/driver_mcdc_report_gate.spl:126 and
src/lib/nogc_sync_mut/test_runner/test_runner_files.spl:703.

## Documented, not fixed this lane

### A. Cross-module struct-return provenance (compiler bug)

Root: a local-fn call returning an IMPORTED struct registers neither
`struct_value_syms` nor a `Named` HIR type on the result local on the flat
native path, so field projections and methods on the value cannot recover
the owner. `remember_call_hir_return` (expr_dispatch.spl:2080) runs but its
sources (`bootstrap_fn_ret_shape_lookup` name registry,
`resolved_call_hir_return_type` via fn_return_types/symbol type) both miss.
The annotation workaround works because the annotated Let registers the
Named HIR type directly. A proper fix belongs to a compiler lane with
bootstrap validation; grep for unannotated `val x = imported_fn(...)` sites
will find more instances once the matrix logs update.

### B. gui_shell_core.spl import surface incomplete + duplicate definitions

`src/app/editor/gui_shell_core.spl` uses ~15 project names
(`gui_shell_render_frame`, `_parse_mouse_coords`, `_drag_state_new`,
`gui_handle_mouse_*`, `platform_default_config`, `GuiBackendConfig`, ...)
without importing them, and `gui_shell.spl` / `gui_shell_render.spl` define
DUPLICATES of several (`gui_shell_render_frame`, `_drag_state_new`,
`gui_handle_mouse_down` in both). The seed resolves these via a
workspace-wide fallback; strict HIR requires explicit imports, and the
duplicates make the "correct" import ambiguous. Needs an owner decision on
which of gui_shell/gui_shell_render is canonical before imports can be
added; until then gui_shell_core stays strict-unbuildable.

### C. Orphaned `draw_ir_fractional_rect`

`src/lib/skia/bridge/picture_draw_ir.spl` imports and calls
`draw_ir_fractional_rect`, which is declared NOWHERE in src/ (latent dead
code — nothing imports picture_draw_ir, so no closure has compiled it
strictly yet). When it enters a closure it will fail with "unresolved name".
The natural definition is a v4 fractional-geometry variant of
`draw_ir_rect` (draw_ir.spl:253) setting `fractional_geometry =
Some(DrawIrFractionalGeometry(...))`; left unimplemented pending an owner
decision on the intended integer x/y/width/height coercion.
