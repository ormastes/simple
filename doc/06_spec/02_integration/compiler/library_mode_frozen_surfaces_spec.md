# library_mode_frozen_surfaces_spec

Manual companion for `test/02_integration/compiler/library_mode_frozen_surfaces_spec.spl`. Source-authored; not generated execution evidence.

Status: **NOT_RUN**. 3 authored cases; 0 executed, 0 passed. Requires the verified Phase3 compiler and matching runtime described in `doc/03_plan/sys_test/configured_library_mode_native.md`.

1. coexists with an explicit GC owner and resolves a common re-export"
2. replays physical declarations with the same owner mode and rejects a changed mode"
3. refuses changed mode against a retained no-import corpus before replay"

Each case uses production APIs and named `step("...")` actions. Missing real fixtures fail; no closed prerequisite gate is counted as feature success. Retain failed or blocked counts and actual artifacts when execution becomes available.
