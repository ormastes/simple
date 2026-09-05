# native-build of MCP closure dies at parse 11/61: `.len()` on i64 in flat-AST encoder (arm_body erasure)

Date: 2026-08-31. Host: Windows 11, seed `bin/simple.exe` (Rust bootstrap seed).
Status: encoder-side FIXED in `src/compiler/10.frontend/core/_Ast/decl_nodes.spl`;
the underlying seed interpreter bug (nested `[[i64]]` arena element erasure)
remains OPEN.

## Symptom

`native-build src/app/mcp/main.spl` aborted at parse 11/61 with

    error: semantic: method `len` not found on type `i64` (receiver value: 38)

and **no file:line**. MCP runs perfectly in source mode; hello-world native-build
got past parse. The file being parsed at death was
`src/std/nogc_sync_mut/io_runtime.spl` (#11 of the 61-file closure); with that
file stubbed the same error moved to `src/std/nogc_sync_mut/io/process_ops.spl`
(receiver value 254) — the trigger is any file whose parse populates match-arm
bodies, not those files' content per se. Content bisection pinned the trigger to
a `match`/`case Ok(x): x` one-liner (receiver value tracked the truncation:
38 → 35), i.e. the receiver is an ERASED stmt-arena id.

## Root cause

Known seed defect (see
`stage3_selfhost_parser_case_multielem_pattern_2026-07-17.md` and the comments
at `decl_nodes.spl:1241`): the seed erases the inner list of a nested `[[i64]]`
global arena element to a boxed i64. Every READER of `arm_body` /
`decl_body_stmts` was already routed through the flat `[text]` mirrors
(`arm_get_body` → `arm_body_flat`), but the flat-AST cache ENCODER
(`flat_decl_pools_dump`) still iterated the poisoned nested arenas directly:
`flat_pool_enc_i64_list(arm_body)` → `flat_pool_enc_i64(inner)` → first
statement `var parts: [text] = ["{pool.len()}\n"]` → `.len()` on the erased
i64. Backtrace shape (via `SIMPLE_INTERP_OOB_DEBUG=1`): eval_collection_expr →
eval_literal_expr (f-string) → eval_call_expr → method `len` on Int, two
for-loop/push frames above — exactly the encoder pair.

## Fix (this record's change)

In `flat_decl_pools_dump` (decl_nodes.spl), rebuild `arm_body` and
`decl_body_stmts` from their flat mirrors (`ast_i64_list_split` per entry) and
reassign the arena before encoding — completing the file's documented
mirror-dodge pattern; bytes are unchanged when the arena is healthy.
`check-flat-ast-codec-complete.shs`: PASS — 165 pools. After the fix the MCP
closure parses **61/61** and lowers **hir 61/61**; cache-hit restore verified
(hits=7 misses=0, no crash).

## New (pre-existing) failure point

The build then fails in phase-3 HIR surface-identity validation:
`Missing module surface alias for <module>` for all 61 modules
(`driver_hir_pipeline_lowering.spl:916`,
`driver_stage3_surface_identity_matches`). A no-import hello-world through the
same worker fails identically at step 2/6, so this is general pre-existing
breakage on this Windows host, unrelated to MCP and to this fix. Suspect: the
`\\?\C:\...` extended-length canonical paths visible in the identity-match
inputs. Not diagnosed further here.

## Windows repro caveat

The top-level `bin/simple.exe native-build ...` swallows the worker's output
and dies with "The filename, directory name, or volume label syntax is
incorrect" under MSYS paths. The working repro is the worker directly:

    SIMPLE_NATIVE_BUILD_WORKER=1 SIMPLE_EXECUTION_MODE=interpret \
      bin/simple.exe run src/app/cli/native_build_worker.spl \
      src/app/mcp/main.spl -o build/w4mcp/mcp.exe

## Spanless diagnostic (separate defect, Rust seed — recorded, not edited)

The message is emitted by `interpreter_method/mod.rs:1758-1786` (not only
`error_macros.rs:82`; both format no location). The interpreter ALREADY tracks
`get_current_file()` (`interpreter_state.rs:912`) and a thread-local
`DEBUG_CALL_STACK` of .spl frames (`debug_call_stack_snapshot()`,
`interpreter_state.rs:723`, used by `note_enum_payload_function`). Minimal
change, error-path-only cost: in the method-not-found construction in
`interpreter_method/mod.rs` (and the `bail_unknown_method` macro in
`error_macros.rs`), add
`ctx = ctx.with_note(format!("in {}; call stack: {}", get_current_file()..., debug_call_stack_snapshot() tail))`.
That alone would have named `flat_pool_enc_i64` ← `flat_pool_enc_i64_list` ←
`flat_decl_pools_dump` and saved this whole bisection. A true span would
additionally require threading the call-site Expr's span id into
`evaluate_method_call`, which today receives only `&Box<Expr>` with no span.
