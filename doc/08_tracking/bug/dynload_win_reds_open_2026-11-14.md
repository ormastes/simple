# Dynload specs still red on Windows (2026-11-14) - status: open

Fixed here (verification-pending): scope leak in `gui_smf_artifact_contract`; host SMF platform id on non-Linux hosts (seed ignores `@cfg(<os>)`, class c, worked around with `@when(os=...)`); admitted fixture platform byte (SmfWriter.create hard-codes Platform.Linux); per_target_build `{triple}` interpolation; BLOCKED message for missing libsimple_runtime.a.

Open:
- `dynsmf_session_close` on a really-admitted load: seed on Windows yields empty `loaded` / hangs (probe exceeded 500 s). Needs native-release owner investigation (smf_dlclose / _smf_dynlib_release_mappings_locked_v3 on Windows).
- product_dynload_startup: fabricated handles 101/102 are rejected by the V3 owner gate; rewrite spec on the admitted fixture.
- l06_dynload_acceptance_v2: missing `fixtures.acceptance_inventory_v2`.
- per_target_build: spec ahead of tree (40 examples), see classes table.
- aspect_dynload_lane_plan: 9 plan-state rows, not Windows-specific.
- SmfWriter.create should take host platform instead of hard-coded Linux.
