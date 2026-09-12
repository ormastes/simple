# sspec GATE scores — specs added since bb1b9cab706 (2026-09-12)

Scored with `analyze_sspec_text` (the same function
`src/app/test_runner_new/sspec_score_gate.spl` uses, default min 80) via a
one-off driver run under the fresh Sep-7 seed
`bin/release/aarch64-apple-darwin-macho/simple_seed` (the pinned
`scripts/check/sspec-score-seed-lane.shs` reshaper lane could not parse
current source on this host — it failed on `src/app/sspec_maintain/main.spl`
itself with a stale-grammar parse error — so the driver called
`analyze_sspec_text` directly instead). 83 `*_spec.spl` files were added in
the range; 31 scored below the 80 gate and were fixed with minimal structural
edits only (docstrings, `step()`, `# @req`, `# @capture`) — no assertion was
weakened or removed, and every edited file was re-run under the seed to
confirm 0 failures after editing.

## Files edited (before -> after)

| spec | GATE before | GATE after |
|---|---|---|
| test/01_unit/app/ui/gpu_boundary_audit_spec.spl | 49 | 89 |
| test/01_unit/app/ui/layout_geometry_diff_spec.spl | 49 | 91 |
| test/01_unit/app/ui/renderdoc_capture_lane_receipt_spec.spl | 49 | 89 |
| test/01_unit/browser_engine/border_radius_antialias_engine2d_spec.spl | 49 | 84 |
| test/01_unit/browser_engine/border_radius_antialias_spec.spl | 49 | 99 |
| test/01_unit/browser_engine/box_shadow_falloff_spec.spl | 49 | 86 |
| test/01_unit/browser_engine/compound_attribute_selector_spec.spl | 49 | 88 |
| test/01_unit/browser_engine/css_math_length_spec.spl | 49 | 82 |
| test/01_unit/browser_engine/flex_wrap_auto_width_item_spec.spl | 49 | 88 |
| test/01_unit/browser_engine/flex_wrap_grow_distribution_spec.spl | 49 | 88 |
| test/01_unit/browser_engine/form_control_ua_font_spec.spl | 49 | 88 |
| test/01_unit/browser_engine/grid_repeat_minmax_track_list_spec.spl | 49 | 88 |
| test/01_unit/browser_engine/inline_content_area_half_leading_spec.spl | 49 | 82 |
| test/01_unit/browser_engine/inline_run_advance_and_break_boxes_spec.spl | 49 | 88 |
| test/01_unit/browser_engine/paint_layout_advance_parity_spec.spl | 49 | 91 |
| test/01_unit/browser_engine/style_cascade_memo_spec.spl | 49 | 88 |
| test/01_unit/lib/gpu/web_route_stage_counters_spec.spl | 49 | 83 |
| test/unit/browser_engine/border_radius_antialias_engine2d_spec.spl | 49 | 84 |
| test/unit/browser_engine/border_radius_antialias_spec.spl | 49 | 94 |
| test/unit/browser_engine/box_shadow_falloff_spec.spl | 49 | 86 |
| test/unit/browser_engine/compound_attribute_selector_spec.spl | 49 | 88 |
| test/unit/browser_engine/css_math_length_spec.spl | 49 | 82 |
| test/01_unit/app/ui/renderdoc_diff_spec.spl | 79 | 84 |
| test/01_unit/bugs/interp_struct_local_copy_aliasing_spec.spl | 79 | 91 |
| test/01_unit/bugs/jit_substring_chained_to_int_spec.spl | 79 | 87 |
| test/01_unit/bugs/jit_wide_i64_storage_roundtrip_spec.spl | 79 | 87 |
| test/01_unit/bugs/spec_expect_fires_in_later_describe_blocks_spec.spl | 79 | 87 |
| test/01_unit/lib/gpu/engine2d/vulkan_image_key_and_flush_site_spec.spl | 79 | 84 |
| test/02_integration/gpu/engine2d_vulkan_damage_scoped_mirror_spec.spl | 79 | 84 |
| test/02_integration/gpu/engine2d_vulkan_readback_unpack_cost_spec.spl | 79 | 87 |
| test/05_perf/interp/interpreter_component_scaling_spec.spl | 79 | 84 |

## Fix pattern

Almost every score-49 file shared one root cause: a `# @req: REQ-...`
traceability comment placed between the file's top `"""` docstring and the
`use` imports — outside both the docstring and any `it` body, which trips
the SSDOC-TRC-003 **blocker** (any REQ id outside a docstring or `it` body
clamps the whole file's score to 49 regardless of everything else). Fix:
wrap the REQ line in its own `"""..."""` docstring in place (no need to
merge into the existing one). The score-79 files lacked `step("...")` calls
inside `it` bodies (SSDOC-BEH-001) and/or an authored `## Purpose and
audience` docstring section (SSDOC-NAR-001) and per-scenario `# @req`
traceability (SSDOC-TRC-001); fix: add `step(...)`, `# @req REQ-<ID>-NNN`,
and `# @capture(assertion): ...` inside each `it` body, plus a `## Purpose
and audience` paragraph in the top docstring.
`test/01_unit/app/ui/layout_geometry_diff_spec.spl` was restructured from an
ad hoc `fn main()` + `check()` counter format into proper `describe`/`it`/
`expect` scenarios (same 12 assertions, same production calls, zero behavior
change) because SSDOC-ORA-001 requires the assertions live inside real `it`
bodies.

## Deliberate exception — NOT fixed (min=49 stands)

| spec | GATE | why left alone |
|---|---|---|
| scripts/check/fixtures/test_runner_calibration_green_spec.spl | 49 | |
| scripts/check/fixtures/test_runner_calibration_red_spec.spl | 49 | |
| scripts/check/fixtures/test_runner_calibration_zero_spec.spl | 49 | |

These three are single-purpose calibration fixtures for
`scripts/check/check-test-runner-executes-bodies.shs`, deliberately kept out
of `test/` so whole-suite discovery never picks them up. Their whole job is a
trivial, self-contained literal assertion (`expect(1).to_equal(1)` /
`to_equal(2)`) so the calibration script can prove the runner executes `it`
bodies rather than load-checking the file; the zero-fixture deliberately
declares no `it` at all to prove the runner reports "0 executed" as an ERROR.
SSDOC-ORA-001/ORA-002 (no real production oracle / tautological literal
comparison) are blockers here by design — replacing the literal assertion
with a real production call would defeat the fixture's calibration purpose,
which the task's "never weaken assertions or change behavior" rule forbids
touching. `green`/`red` did get a docstring + `step()` + `@req` +
`@capture()` added (cosmetic only, does not change pass/fail behavior) but
the two ORA blockers are inherent to the fixture's design and were left in
place; `zero` was left untouched entirely since adding an `it` would also
defeat its purpose.

## Summary

- 83 specs scored (GATE, `analyze_sspec_text`)
- 34 scored below 80 before this change (31 fixed to >=80; 3 deliberate
  fixture exceptions unchanged)
- min after: 49 (the 3 exceptions); excluding them, min after = 82
- median after (all 83): 87
- Every edited file was executed under the seed post-edit: 0 new failures.
