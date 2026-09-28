# PR #1870 / #1830 merged without passing review: remaining work

- **Date:** 2026-09-28
- **Status:** open. The fix-forward PR fixed parse errors and the `.py` violation and tagged the red specs. The items below still need the feature owners.
- **Merged:** #1870 "feat(2d): harden Simple 2D/Web/GUI with optional upstream Skia" (merge `7b8a48cc510`) and #1830 "WIP: profile-switchable containers and profile feedback". Both merged around 01:54-02:01Z. Review for both said not to land.
- **Measured on:** `bin/release/aarch64-unknown-linux-gnu/simple`, run once per spec with `timeout 600 bin/simple test <spec>`.

## What the fix-forward PR already did

1. Ported `tools/upstream-skia-ganesh-vulkan/verify-skia-deps.py` to `verify-skia-deps.shs` and deleted the `.py`. `build-linux.shs` and `build-macos.shs` now call the new script.
   - Checked against the real pinned Skia DEPS (`35d5edfa0d5`, 45 Git deps) on a synthetic checkout. Both scripts wrote the same manifest bytes and the same sha256.
   - Both scripts also gave the same exit code 2 and the same message for five failures: dirty dep, wrong rev, sync disabled, not its own checkout, and unpinned rev.
   - One difference: a DEPS line the awk parser does not recognise now fails with exit 2. The Python `exec` path crashed with exit 1 instead.
   - The review suggested pinning the dependency count in `skia-pin.json`. That was **not** done, because the port had to keep identical behaviour. It is an open follow-up.
2. Rewrote multi-line inline `if/else` expressions into block form in four files:
   - `provider.spl`: 5 `Err(if ...)` sites and the `bytes` readback.
   - `physical_vulkan_2d_qualification.spl`: the oracle prefix and the candidate reason.
   - `gui_button_qualification.spl`: the button color.
   - `src/app/optimize/collection_plan_cli.spl` (from #1830): `live_collision_guard`, whose trailing `[` was being parsed as an index.
   `physical_vulkan_2d_qualification_spec` is now green (it was red before). `collection_plan_cli_spec` went from a parse error to 6 of 7 passing.
3. Fixed broken indentation at `web_corpus_case01_stage1_spec.spl:45-48`, which caused `expected expression, found Indent`.
4. Tagged 34 red specs `# @tag:in-development`, each with a `# Tracks:` line pointing at this file. They are listed below.

## Parser bug: a line break right after `if <cond>:` in expression position

Filed here as the repo rule requires:

```simple
val x = if c:
    1 else: 2          # parse: Unexpected token: expected expression, found Else
```

Also fails: `val p = if c:\n    "a" else:\n    "b"`.

These parse fine on the same binary: `Some(if c: "a" else:\n    "b")`, and an inline if inside a multi-line argument list.

The reviewer's binary also rejected `Err(if c: "a" else:\n "b")` at `provider.spl:479`. So the accepted set depends on the binary.

Either the grammar accepts the break-after-colon form, or the linter should reject it.

## #1870 still needs

- **`common.ui.ui_ir` module** (`UiIr`, `UI_IR_COMMAND_RECT`, `draw_ir_to_ui_ir`). It does not exist, yet `src/lib/skia/backend/upstream_ganesh_vulkan/provider.spl:9` imports it. The plan (`doc/03_plan/ui/unified_surface_draw_ir_and_html_css_conformance.md:110-112`) gates it on the field/layout design passing first. Because of this, the whole upstream provider does not load today.
- **`std.gc_async_mut.gpu.browser_engine.web_opaque_box_qualification` module** (for example `web_corpus_case01_gpu_scene_from_html`). It does not exist. These import it: 4 `*_capture_artifact.spl` files under `src/lib/skia/backend/upstream_ganesh_vulkan/`, `src/app/test/vulkan_2d_qualification/scene_contract.spl`, and 7 specs.
- **Missing functions:** `corpus_case31_analytic_oracle` (breaks `web_corpus_case31_stage1`, 1 of 4) and `simple_web_layout_render_html_draw_ir_fractional_result` (breaks `web_fractional_case02_v4`).
- **Hardware lane:** `STATUS: FAIL`. Physical Linux Vulkan render and readback are required.

## #1830 still needs

These come from its PR body and `doc/09_report/profile_switchable_container_status_2026-09-26.md`. Item 7 is **STATUS: FAIL**.

- **Source-matched runner:** admit a pure-Simple runner that matches the source, then run the item-7 specs on the pure-Simple, interpreter and LLVM-native backends. None of them has passed yet.
- **Deploy what the specs need.** The deployed interpreter lacks:
  - the externs `spl_ordered_key_cmp`, `spl_collection_capture_note_size` and `spl_collection_capture_begin`. They are defined in `src/runtime/runtime_native.c:4479/4663`, but the interpreter does not know them.
  - the new `@collection_algorithm(...)` attribute on `var` declarations. The parser reports `expected Fn, found Var/Identifier`.
  - `HashMap.with_capacity`, which dispatches to `dict` on the deployed binary.
  - the module `test.system.qualified_pure_simple_runtime`, which does not exist.
  - Also: `native_build_warm_collection_profile_spec` hits `nil ... 'file_hash_sha256'`.
- **Ordered-key gap:** typed aggregate `Ord` dispatch and generic `Ord` enforcement are not done (status report lines 9, 11 and 29).
- **Typed-planner gap:** the CollectionPlan is not connected to HIR/MIR selection (`guard.typed_mir=unconnected`), and the CLI `--explain-collection-plan` is not wired (status report lines 13, 27, 49 and 59).
- **Hang:** `hash_lookup_observation_spec` hit the 600 s timeout (rc 124). Find out why before it is promoted.

2026-09-28 item 7 follow-up: source inspection found the hang path in a
capacity-one `HashSet`. After one insertion every slot is occupied; a missing
key made `contains` probe forever, and `remove` had the same unbounded loop.
Both scans now stop after `capacity` probes, and the focused spec checks the
missing-key lookup and removal. This is an implementation correction, not a
PASS receipt: the spec remains tagged until it runs on an admitted,
source-matched pure-Simple runtime on Windows and WSL.

## Tagged specs (34)

When a spec starts passing, remove its tag in the same commit as the fix and delete it from this list.

#1870 (14): `test/03_system/app/ui/feature/`
- `corpus_case01_physical_capture`
- `corpus_case06_physical_capture`
- `gui_widget_vulkan_producer`
- `html_css_corpus_producer`
- `simple_2d_skia_renderdoc_hardening`
- `web_corpus_case01_stage1`
- `web_corpus_case02_gpu_projection`
- `web_corpus_case06_stage1`
- `web_corpus_case31_stage1`
- `web_decimal_geometry_provenance`
- `web_fractional_case02_v4`
- `web_fractional_leaf_producer`
- `web_opaque_box_physical_capture`
- `web_opaque_box_stage1`

Each file name ends in `_spec.spl`.

#1830 (20):
- `test/01_unit/app/cli/native_build_warm_collection_profile`
- `test/01_unit/app/io/_CliCompile/native_collection_profile_snapshot`
- `test/01_unit/app/optimize/{collection_plan_cli,sprof_collection_profile}`
- `test/01_unit/compiler/parser/collection_algorithm_attribute`
- `test/01_unit/lib/nogc_sync_mut/src/collections/`:
  - `adaptive_float_key_equivalence`
  - `adaptive_generic_collections`
  - `adaptive_generic_profile`
  - `adaptive_text_map`
  - `adaptive_text_set`
  - `hash_lookup_observation`
  - `ordered_map`
- `test/02_integration/compiler/profile_switchable_{attribute,cli_feedback,native_feedback}_it`
- `test/03_system/app/compiler/feature/profile_switchable_container_algorithms`
- `test/05_perf/collections/profile_switchable_{hash_probe,linear_operation_count,ordered_operation_count}`

These specs from the two PRs pass and are **not** tagged:
- `engine2d_bridge`
- `html_css_corpus_integrity`
- `physical_vulkan_2d_qualification`
- `upstream_skia_physical_capture_artifact`
- `collection_plan_explain`
- `collection_plan_selection`
- `ordered_text_set`
