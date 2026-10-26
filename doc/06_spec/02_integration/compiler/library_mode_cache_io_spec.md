# library_mode_cache_io_spec

Manual companion for `test/02_integration/compiler/library_mode_cache_io_spec.spl`. Source-authored; not generated execution evidence.

Status: **NOT_RUN**. 2 authored cases; 0 executed, 0 passed. Requires the verified Phase3 compiler and matching runtime described in `doc/03_plan/sys_test/configured_library_mode_native.md`.

1. stores and reloads interleaved modes in one real private cache"
2. roundtrips the configured archive mode and refuses invalid mode envelopes"

Each case uses production APIs and named `step("...")` actions. Missing real fixtures fail; no closed prerequisite gate is counted as feature success. Retain failed or blocked counts and actual artifacts when execution becomes available.
