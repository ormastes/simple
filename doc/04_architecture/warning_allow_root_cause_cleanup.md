# Architecture: Warning/Allow Root-Cause Cleanup

## Ownership

- Rust enforcement owner: `.github/workflows/rust-tests.yml`
- Simple enforcement owner: `.github/workflows/simple-strict-lints.yml`
- Regression canary owner: `test/code_quality/warning_allow_root_cause_cleanup_spec.spl`
- Strict Rust compile prerequisites: `src/compiler_rust/runtime/**`
- Decorator whitelist ownership: `src/compiler_rust/compiler/src/lint/**`

## Rollout

1. Repair the enforcement path so the strict commands actually execute on this
   repository layout.
2. Fix the current Rust strict-gate blockers that prevent baseline collection.
3. Add a targeted Simple `--deny-all` lane using existing low-noise canaries.
4. Preserve advisory-only workflows outside the owned enforcement path.

## Suppression Taxonomy For This Slice

- Fixed directly:
  - workflow-path drift for the Rust strict lane
  - runtime compile failure blocking strict Rust linting
  - low-risk Clippy style debt in the primitive-sort benchmark
  - stdlib decorator whitelist drift in the Rust lint checker
- Explicitly deferred:
  - broad workspace-level Rust `allow` table removal
  - whole-tree Simple `unnamed_duplicate_typed_args` cleanup
  - broad `export_outside_init` restructuring
  - cross-platform/editor/bootstrap advisory workflow tightening
