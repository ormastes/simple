# warning_allow_root_cause_cleanup_spec was prose only: parse-error, 0 executed

- Status: verification-pending
- Date: 2026-11-28
- Spec: test/03_system/app/tooling/feature/warning_allow_root_cause_cleanup_spec.spl

## Root cause
The spec file body was markdown scenario prose (`## Scenario`, `- Given/When/Then`)
with no `describe`/`it` code, so the parser rejected it
(`SPEC FILE VERDICT ... reason=parse-error`, executed=0). Not a parser defect:
bare prose is not valid Simple.

## Fix
- Rewrote `test/03_system/app/tooling/feature/warning_allow_root_cause_cleanup_spec.spl`
  as executable `describe`/`it` blocks covering the same three scenarios:
  1. `rust-tests.yml` uses `working-directory: src/compiler_rust` and `-D warnings`.
  2. `simple-strict-lints.yml` runs `--deny-all` over
     `test/03_system/quality/code_quality/warning_allow_root_cause_cleanup_spec.spl`,
     which exists as the canonical quality canary on `release/1.0.0`.
  3. `src/compiler_rust/runtime/src/value/primitive_sort.rs` exposes
     `const NEON_I64_RADIX_MIN_LEN` and `const NEON_F64_RADIX_MIN_LEN`.

## Prevention
The spec itself is executable SSpec pinning the workflow configuration, canary
path, and runtime constants so `simple test` executes all three assertions.

## Verification
Rebased onto `origin/release/1.0.0`, preserved `.github/workflows/simple-strict-lints.yml`
targeting `test/03_system/quality/code_quality/warning_allow_root_cause_cleanup_spec.spl --deny-all`,
and verified all local structural/ratchet gates.
