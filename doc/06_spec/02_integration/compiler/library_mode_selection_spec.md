# library_mode_selection_spec

Manual companion for `test/02_integration/compiler/library_mode_selection_spec.spl`. Source-authored; not generated execution evidence.

Status: **NOT_RUN**. 6 authored cases; 0 executed, 0 passed. Requires the verified Phase3 compiler and matching runtime described in `doc/03_plan/sys_test/configured_library_mode_native.md`.

1. selects distinct physical owners for the same generic import"
2. rejects a leaf that exists only in an unselected family"
3. keeps an explicitly imported internal owner's generic dependency coherent"
4. keeps the unconfigured legacy family order"
5. interleaves real source cache keys and parser bindings without ambient mode"
6. keeps application selection beneath an unrelated lib family ancestor"

Each case uses production APIs and named `step("...")` actions. Missing real fixtures fail; no closed prerequisite gate is counted as feature success. Retain failed or blocked counts and actual artifacts when execution becomes available.
