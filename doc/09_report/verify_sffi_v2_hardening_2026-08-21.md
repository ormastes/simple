# SFFI v2 hardening verification — 2026-08-21

## Scope

Verification covers the bounded P0 return-contract, dynamic-interpreter, and
native status-path changes plus the P0/P1 research, requirements, architecture,
design, plans, guide, and executable specification. P1 typed registry/thunks
and P2-P6 remain planned and are not claimed complete.

## Results

- PASS: `simple-runtime` focused `wsffi_native` tests — 4 passed, 0 failed,
  0 ignored.
- PASS: numbered-artifact guards for working and staged changes.
- PASS: direct-env/runtime guards for working and staged changes.
- PASS: `doc/06_spec` contains zero executable `*_spec.spl` files.
- PASS: changed-diff whitespace check after documentation cleanup.
- FAIL: focused `simple-compiler` tests did not execute. The rebased upstream
  compiler fails first because `compiler/src/interpreter/expr.rs` references
  missing module `crate::interpreter::dispatch_profile` (`E0433`).
- FAIL: pure-Simple SPipe/docgen and required compiler/lib/MCP smoke checks
  cannot be admitted until a current self-hosted compiler builds and runs.
- FAIL: sabotage and cross-lane interpreter/JIT/native/SimpleOS evidence are
  incomplete.
- FAIL: native generic i64/f64 value bridges still collide on zero for invalid
  inputs; migration to status/out or `Result` ABI is tracked in the dynamic
  SFFI bug record.

## Status

**STATUS: FAIL** — suitable for pushing as an explicitly partial hardening and
design checkpoint, but not for release or a claim that SFFI v2 is complete.
