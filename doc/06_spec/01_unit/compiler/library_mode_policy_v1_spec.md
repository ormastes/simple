# library_mode_policy_v1_spec

Manual companion for `test/01_unit/compiler/library_mode_policy_v1_spec.spl`. Source-authored; not generated execution evidence.

Status: **NOT_RUN**. 6 authored cases; 0 executed, 0 passed. Requires the verified Phase3 compiler and matching runtime described in `doc/03_plan/sys_test/configured_library_mode_native.md`.

1. derives all eight GC concurrency mutability selections"
2. admits only the implemented noalloc combination"
3. accepts split and inline CLI values and rejects duplicates or missing values"
4. does not turn a legacy allowlist into explicit selection"
5. checks explicit typed options and preserves internal owner coherence"
6. separates configured invocation identities from equivalent legacy restrictions"

Each case uses production APIs and named `step("...")` actions. Missing real fixtures fail; no closed prerequisite gate is counted as feature success. Retain failed or blocked counts and actual artifacts when execution becomes available.
