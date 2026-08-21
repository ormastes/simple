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
- PASS: focused return-contract tests — 5 passed, 0 failed, 0 ignored.
- PASS: focused dynamic-SFFI tests — 12 passed, 0 failed, 0 ignored. Their
  stable-code assertions inspect the authoritative rich diagnostic context.
- PASS: the tracked dispatch profiler is restored to the interpreter module
  tree, removing the upstream `E0433` compiler-test blocker.
- FAIL: pure-Simple SPipe/docgen and required compiler/lib/MCP smoke checks
  cannot be admitted: the deployed `bin/simple` reports that it is a Rust-built
  bootstrap seed, so it is not valid self-hosted production evidence.
- FAIL: sabotage and cross-lane interpreter/JIT/native/SimpleOS evidence are
  incomplete.
- FAIL: native generic i64/f64 value bridges still collide on zero for invalid
  inputs; migration to status/out or `Result` ABI is tracked in the dynamic
  SFFI bug record.

## Status

**STATUS: FAIL** — the bounded Rust-backed P0 unit tests pass, but this remains
an explicitly partial hardening and design checkpoint, not release evidence or
a claim that SFFI v2 is complete.
