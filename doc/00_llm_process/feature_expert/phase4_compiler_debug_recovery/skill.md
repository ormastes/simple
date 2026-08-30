# Phase 4 compiler debug recovery feature expert

## Mission

Recover and qualify the x86_64 full CLI without weakening compiler semantics or
promoting bootstrap diagnostics. The only acceptance authority is an admitted,
current-source pure-Simple Stage 4 candidate produced by an admitted
pure-Simple Stage 3.

## Evidence hierarchy

1. Retain the earliest broken compiler boundary and its artifacts.
2. Use Rust-seed runs only to diagnose bootstrap production.
3. Admit Stage 4 with
   `scripts/check/check-post-bootstrap-stage4-sspec.shs`.
4. Execute
   `test/03_system/compiler/phase4_compiler_debug_recovery_spec.spl` with that
   exact candidate.
5. Deploy only after all rows pass; require deployed/candidate SHA-256 equality.

Never describe Rust-seed, Stage 2/3, replayed LLVM, a skipped DAP smoke, or a
stale installed wrapper as Stage 4 runtime evidence.

## Frozen operator contract

The spec consumes `PHASE4_DEBUG_CANDIDATE`, `PHASE4_DEBUG_PROVENANCE`,
`PHASE4_DEBUG_DEPLOYED`, and `PHASE4_DEBUG_ARTIFACT_ROOT`. Its shared helpers
are `required_env`, `shell_quote`, `run_shell`, `run_candidate`,
`expect_command_pass`, `expect_command_rejected`, `text_absent`,
`verify_stage4_admission`, and `verify_deployed_hash_binding`. Preserve these
names when extending the lane so the manual and future sidecars share one
vocabulary.

## Debug classification

Use `doc/07_guide/app/llm/llm_bootstrap_llvm_debugging.md` to classify HIR,
MIR, LLVM assembly, verification, and target-codegen failures. Do not make a
later layer accept invalid output from an earlier layer. Replay is diagnostic;
candidate construction and admission remain mandatory.

## Acceptance boundary

The exact candidate must pass compiler/lib/MCP/LSP checks, the real MCP stdio
integration, a native C5 `char_from_code` fixture with exit `42`, and canonical
DAP smoke with explicit PASS and no SKIP. Deployment completes only when its
hash equals the admitted candidate. Missing runtime means `TEST_BLOCKED`.

## Current state

The system artifacts are implemented but not executed because no admitted
current-source Stage 4 exists. No runtime PASS is claimed.
