# Dynload specs still red on Windows (2026-11-14) - status: open

Fixed here (verification-pending): scope leak in `gui_smf_artifact_contract`; host SMF platform id on non-Linux hosts (seed ignores `@cfg(<os>)`, class c, worked around with `@when(os=...)`); admitted fixture platform byte (SmfWriter.create hard-codes Platform.Linux); per_target_build `{triple}` interpolation; BLOCKED message for missing libsimple_runtime.a.

Open:
- `dynsmf_session_close` empty `loaded` (verification-pending, 2026-11-14 lane dynclose): NOT a close/release defect and NOT a hang. `smf_dlclose` and the in-place row update work (probe: loaded=1 before and after close, 2 evidence rows). Root cause was spec hygiene: symbol bindings are process-global, `dynsmf_lifecycle_close_spec` example 2 (and the reload/stale examples) never closed their sessions, so every later load of `render_lifecycle` failed with "Symbol render_lifecycle is already bound" (`loaded` stays empty), and the seed `it` body continues after `fail(...)`, which then indexed `loaded[0]` (OOB). Fix: the examples close their sessions. Before 2/8 green, after 5/8 (remaining 3 are explicit owner-missing EXPECTED REDs). Regression: `dynsmf_close_releases_symbol_binding_spec` (2/2). The 500 s hang was not reproduced (spec runs in seconds). Seed note: `fail()` not aborting the example is a seed behaviour worth a separate record. `dynsmf_session_unload_reload_spec` is 4/5; its remaining red (`artifact_missing_file` vs "admitted") is not close related.
- Release tip parse failure (tagged workaround): `src/compiler/00.common/driver_compile_options.spl:63` has a `val reason = match ...` followed by a multi-line array literal as the tail expression; seed-attr and seed-tip both fail with `expected RBracket, found Comma` (the literal is parsed as an index of the match arm). Workaround here: bind the array to `val fields` and return it. Needs a seed parser fix (match tail followed by a `[` line).
- product_dynload_startup: fabricated handles 101/102 are rejected by the V3 owner gate; rewrite spec on the admitted fixture.
- l06_dynload_acceptance_v2: missing `fixtures.acceptance_inventory_v2`.
- per_target_build: spec ahead of tree (40 examples), see classes table.
- aspect_dynload_lane_plan: 9 plan-state rows, not Windows-specific.
- SmfWriter.create should take host platform instead of hard-coded Linux.
