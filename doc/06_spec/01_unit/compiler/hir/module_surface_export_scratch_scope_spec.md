# Streaming export-origin scratch lifetime

Requirement: REQ-EXPORT-SCRATCH-001.
Executable: `test/01_unit/compiler/hir/module_surface_export_scratch_scope_spec.spl`.

- A facade preceding its leaf retains the split alias and resolves the same
  terminal declaration after scope teardown and fixpoint revisits.
- Two wildcard owners produce an ambiguity whose text survives cleanup;
  a subsequent scope can begin successfully.
- An existing caller scope is rejected without being closed by the resolver.

Native SSpec execution is pending. The macOS canonical jobs=8 compiler must
peak below 1,000,000,000 bytes RSS. Measured failures and the remaining bounded
cycle are documented in
`doc/08_tracking/bug/stage3_macos_compile_peak_rss_2026-09-21.md`.
