# Phase 4 compiler debug recovery

## Purpose and audience

This operator manual qualifies one exact pure-Simple Stage 4 compiler after
bootstrap debugging. It is for compiler/bootstrap owners preparing a local
deployment. It cannot turn Rust-seed, Stage 2, Stage 3, skipped-tool, or stale
binary evidence into a Stage 4 PASS.

## Current status

`TEST_BLOCKED`: no admitted current-source Stage 4 runtime exists. The
executable specification has not been run, and this manual records no runtime
PASS. It is ready to execute once the qualified environment exists.

## Preconditions

Set these values to absolute, canonical paths:

- `PHASE4_DEBUG_CANDIDATE`: executable Stage 4 candidate.
- `PHASE4_DEBUG_PROVENANCE`: adjacent `simple.provenance.env` receipt.
- `PHASE4_DEBUG_DEPLOYED`: local deployed `simple` executable.
- `PHASE4_DEBUG_ARTIFACT_ROOT`: new or lane-owned output directory for the C5
  character probe.

The candidate must already be produced by an admitted pure-Simple Stage 3.
The Rust seed may diagnose bootstrap, but it must not execute this spec.

## Operator workflow

1. Require all four canonical inputs and reject seed identity or substituted
   provenance (`REQ-P4DBG-001`).
2. Run `scripts/check/check-post-bootstrap-stage4-sspec.shs` and require exact
   binary, source, Stage 3 parent, and unchanged smoke-log admission markers
   (`REQ-P4DBG-002`).
3. Run candidate `check` for `src/compiler` and `src/lib`
   (`REQ-P4DBG-003`).
4. Run candidate `check` for `src/app/mcp` and `src/app/simple_lsp_mcp`
   (`REQ-P4DBG-004`).
5. Run the real MCP stdio integration with `SIMPLE_LIB=src` and no stub
   fallback (`REQ-P4DBG-005`).
6. Native-build `test/03_system/native/c5_char_from_code.spl` with the
   admitted candidate and require exact exit code `42` (`REQ-P4DBG-006`).
7. Run `scripts/smoke/dap_protocol_smoke.spl`, require its explicit PASS and
   reject SKIP, then require the deployed executable SHA-256 to equal the
   admitted candidate SHA-256 (`REQ-P4DBG-007`).

## Execution

Run the executable spec using `PHASE4_DEBUG_CANDIDATE` itself in interpreter
mode with session daemon and cache disabled. The exact command is maintained in
`doc/03_plan/sys_test/phase4_compiler_debug_recovery.md`.

## Pass/fail boundary

PASS requires every command to exit as specified, no failed-file/stub-fallback
marker, an explicit DAP PASS with no SKIP, native C5 exit `42`, and identical
candidate/deployed hashes. Missing paths, malformed provenance, any Rust-seed
identity, timeout, signal, skipped DAP smoke, nonzero check/test exit, wrong C5
exit, or hash mismatch is FAIL.

## Evidence and limitations

Retain the SSpec transcript and C5 output artifact below
`PHASE4_DEBUG_ARTIFACT_ROOT`. This lane proves x86_64 local Stage 4 compiler and
tool admission only. It does not prove release tags, other hosts/CPUs, QEMU,
physical boards, or a new wall-clock bootstrap event.
