# Verification Report: warning_allow_root_cause_cleanup

- PASS: `cargo clippy --workspace --all-targets -- -D warnings` from
  `src/compiler_rust/` completed successfully after fixing the primitive-sort
  compile blocker and the surfaced Clippy debt in `compile_commands.rs` and the
  benchmark helper.
- PASS: `cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-runtime primitive_sort -- --nocapture`
  passed (`10` primitive-sort tests).
- PASS: `cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-compiler lint::tests::test_known_stdlib_module_decorators_no_warning -- --nocapture`
  passed.
- PASS: `src/compiler_rust/target/bootstrap/simple lint ... --deny-all`
  passed for:
  - `test/code_quality/allow_suppressions_spec.spl`
  - `test/code_quality/bare_bool_lint_spec.spl`
  - `test/code_quality/primitive_api_lint_spec.spl`
  - `test/code_quality/warning_allow_root_cause_cleanup_spec.spl`
- PASS: Removed stale `#![allow(unnamed_duplicate_typed_args)]` suppressions
  from:
  - `src/compiler/90.tools/header_gen/c_header.spl`
  - `src/compiler/90.tools/header_gen/cpp_header.spl`
  - `src/compiler/90.tools/header_gen/mod.spl`
  The remaining warnings in those files are unrelated `REQC*` quality findings,
  not duplicate-typed-argument suppressions.
- PASS: Mechanical stale-suppression passes reduced the repo-wide `allow`
  count from `1822` to `1714`.
  Largest category changes in this pass:
  - `unnamed_duplicate_typed_args`: `1029 -> 943`
  - `primitive_api`: `222 -> 196`
  - `bare_bool`: `62 -> 52`
- WARN: `bin/simple lint ... --deny-all` still segfaults locally (`STATUS=139`),
  which matches the existing lint-wrapper instability already tracked in repo
  bug docs. The new authoritative Simple lane therefore uses the bootstrap
  runtime directly instead of the crashing wrapper.
- WARN: attempted removal of several stdlib `#![allow(unknown_attribute)]`
  directives showed the current lint path still flags `@extern(...)` as
  `unknown_attribute`. Those allows remain justified until that root cause is
  fixed.

STATUS: PASS
