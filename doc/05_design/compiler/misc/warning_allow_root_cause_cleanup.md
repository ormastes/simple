# Detail Design: Warning/Allow Root-Cause Cleanup

## Rust Enforcement

- Update `rust-tests.yml` to detect and operate on `src/compiler_rust/`.
- Keep the existing strict Clippy command as the authoritative Rust warning gate.
- Fix the primitive-sort runtime test import break by restoring the explicit
  NEON threshold constants used by the test module.
- Replace the benchmark's redundant comparator closures with `sort_by_key`
  to satisfy strict Clippy without changing behavior.

## Simple Enforcement

- Add `simple-strict-lints.yml` with one required job:
  `strict-simple-lints`.
- Use the bootstrap runtime from `src/compiler_rust/target/bootstrap/simple`
  so CI runs the same compiler artifact it just built.
- Start with stable code-quality canaries:
  - `test/code_quality/allow_suppressions_spec.spl`
  - `test/code_quality/bare_bool_lint_spec.spl`
  - `test/code_quality/primitive_api_lint_spec.spl`
  - `test/code_quality/warning_allow_root_cause_cleanup_spec.spl`

## Regression Canary

- Add a spec that reads workflow/source files directly and asserts:
  - Rust workflow contains `src/compiler_rust`
  - Simple strict workflow exists and contains `--deny-all`
  - primitive-sort runtime still defines the NEON threshold constants

## Deferred Follow-Up

- Once the strict gates are stable, remove broad workspace Rust `allow`s in
  measured batches and expand the Simple strict lane from canaries to owned
  source trees.
- Split `unknown_attribute` follow-up from stale suppression cleanup.
  The remaining stdlib `unknown_attribute` allows around `@extern(...)` are not
  decorative debt; they protect a still-broken classification path and should
  be replaced only after that root cause is fixed.
