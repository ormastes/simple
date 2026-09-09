# Phase 1 verification escaped seed authority and false-passed missing tools

**Date:** 2026-09-08
**Status:** FIXED IN WORKING TREE
**Component:** `scripts/bootstrap/bootstrap-phase-verification.shs`

## Symptom

The retained Phase 1 MCP and LSP MCP logs failed while parsing the valid
constructor call in
`src/compiler/00.common/structural_contracts/frontend_offload_switch.spl`:

```simple
FrontendOffloadSwitch(mode: mode, auto: auto, fallback: ..., source: ..., raw: ...)
```

Both summary rows nevertheless said `result=PASS|status=0`, and neither
expected server executable existed.

## Direct parser evidence

`auto` is deliberately a hard lexer token. The direct stream for
`P(auto: auto)` is `Identifier LParen Auto Colon Auto RParen`. Current
`parse_arguments` accepts `TokenKind::Auto` contextually as a named-argument
label, and a direct parser-crate regression parses the complete
`frontend_offload_switch.spl` source.

The retained failing native-build log instead ends with:

```text
interpreter: C:\Users\User\dev\simple/bin/simple.exe (exit code 1)
```

That path is the ambient deployed pure-Simple CLI, not the admitted Phase 1
snapshot. The source parser was current; the verification command escaped its
authority and delegated to a stale CLI whose parser predated the `auto:` fix.

## Root cause

The Rust seed defaults `native-build` to the pure-Simple command path unless
`SIMPLE_NATIVE_BUILD_RUST=1` is exact. Phase 1 verification invoked the seed
without that bootstrap-only override or a snapshot-bound `SIMPLE_BINARY`.
The outer command then returned zero after its worker failed, and the recorder
treated exit status alone as proof that each tool was built.

## Fix

Phase 1 native-build rows now run with:

```text
SIMPLE_BOOTSTRAP=1 SIMPLE_NATIVE_BUILD_RUST=1
SIMPLE_BINARY=<isolated-work-root>/compiler.snapshot
<isolated-work-root>/compiler.snapshot native-build ...
```

Every compiler CLI, test-runner, MCP, and LSP MCP build row now removes its
prior output first and requires a fresh, regular, non-symlink executable. A
zero exit with no executable is `FAIL`, status 87, `artifact_status=missing`.
A passing row records the exact artifact path and SHA-256.

## Focused evidence

- `cargo test -p simple-parser --test contextual_keyword_identifiers auto_token_parses_contextually_in_the_exact_frontend_offload_source -- --exact`
  — 1 passed.
- `sh test/01_unit/scripts/bootstrap_phase_stage1_native_build_authority_test.shs`
  — PASS for snapshot-bound environment, both entries, fresh tool launch, stale
  output removal, and exit-zero/missing-output rejection.

The full Phase 1 matrix was deliberately not repeated unchanged. Its next run
must use the changed verifier and a new work root so the summary itself proves
the fixed command and artifact contract.
