# Streaming export-origin scratch lifetime

Requirement: REQ-EXPORT-SCRATCH-001.
Executable: `test/01_unit/compiler/hir/module_surface_export_scratch_scope_spec.spl`.

- A facade preceding its leaf retains the split alias and resolves the same
  terminal declaration after scope teardown and fixpoint revisits.
- Two wildcard owners produce an ambiguity whose text survives cleanup;
  a subsequent scope can begin successfully.
- An existing caller scope is rejected without being closed by the resolver.
- Reciprocal profiles compare 32 unscoped resolutions with 8 and 32 streaming
  resolutions, separately for delayed-alias fixpoint and ambiguity cleanup.
  Production heap-registry deltas must be positive and streaming must retain
  fewer objects than unscoped resolution. Every result checks provenance or
  retained diagnostic text, and a subsequent scope must open and close.
- The 32-resolution profile must take less than 10 seconds, less than 16 times
  the unscoped duration plus 100 ms, and less than 12 times the 8-resolution
  duration plus 100 ms. Builder construction and assertions are outside timed
  intervals. Printed evidence includes nanoseconds and retained object counts.
  Thresholds are coarse authored guards, pending native calibration.

Native SSpec execution is pending. The macOS canonical jobs=8 compiler must
peak below 1,000,000,000 bytes RSS. Measured failures and the remaining bounded
cycle are documented in
`doc/08_tracking/bug/stage3_macos_compile_peak_rss_2026-09-21.md`.
