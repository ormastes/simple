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

## Follow-up: interpreter debug raw boundary (2026-08-26)

- PASS (static): both interpreter-debug facades retain 12 used raw declarations,
  each explicitly `unsafe(ffi)` and each call lexically scoped. Their parity
  audit passes, as does the canonical debug authority audit.
- PASS (source check): `bin/simple check` accepts both changed files. The tool
  identifies itself as the Rust bootstrap seed, so this is not a self-hosted
  production-verification result.
- PASS (optimizer review): each mirror reports the same 55 pre-existing
  opportunities, including two collection-capacity suggestions; the status
  repair adds no normal-path loop, allocation, copy, lookup, hash, or dispatch.
- PASS (contract): provider `-1` failures for breakpoint add/remove and nonzero
  CLI-run status now become `Result.Err`; ordinary boolean behavior is unchanged.
- FAIL (global admission): no signed artifact-bound provider admission is
  established by this work. This follow-up does not change the overall FAIL
  status above.

## Follow-up: advanced scalar math raw boundary (2026-08-26)

- PASS (static): twelve fixed-`f64` declarations and thirteen calls in the
  canonical advanced-math facade are explicitly and lexically `unsafe(ffi)`;
  the guard confirms the Rust exports and no per-call admission machinery.
- PASS (behavior): `math_advanced_spec.spl` executes 13/13 examples with zero
  failures; NaN/infinity remain values rather than fabricated error signals.
- PASS (performance review): direct scalar call shape is retained; optimizer
  reports 25 MIR bounds-check opportunities and zero general patterns.
- WARN: checks ran through the bootstrap seed, not a self-hosted production
  binary. No signature or artifact-bound evidence was created, so global SFFI
  admission remains FAIL.
