# Darwin Self-Hosted Bootstrap Wave A Go-To-End Fixes (2026-11-17)

## Summary
Seven root-caused blockers uncovered during the macOS (`aarch64-apple-darwin`) self-hosted `--keep-going --go-to-end` Wave A sweep (`P2 -> P4` and `P2 -> P3a`):

1. **Non-truncating `simple_llvm_<pid>.ll` writes (`src/compiler/70.backend/backend/llvm_backend_tools.spl`)**:
   Under `SIMPLE_BOOTSTRAP=1`, `rt_file_write_text_at(ir_path, 0, llvm_ir)` opened existing PID-keyed temp IR files without `O_TRUNC`. Whenever a later staged module emitted fewer bytes than the preceding module, stale IR bytes remained after metadata definitions, failing `llc` with `expected top-level entity` across `simple_test_runner`, `simple_build_runner`, `simple_mcp_server`, and `simple_lsp_mcp_server`. Fix: delete any existing `ir_path` right before `rt_file_write_text_at(ir_path, 0, llvm_ir)`.
2. **Soft keyword `spawn` rejected in non-arg expression positions (`src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl`)**:
   `val held = match spawn:` failed parsing because token `197` (`TOK_KW_SPAWN`) unconditionally parsed `parse_expr()`. Fix: apply the same `g33_kw_ident_follow` / closing delimiter guard already used for `new`.
3. **Darwin Apple `ld` unsupported ELF/lld trial-link flags (`src/compiler/80.driver/driver_build/go_to_end_trial_link_v1.spl`)**:
   Go-to-end trial links passed `-Wl,--error-limit=0` and `-Wl,--no-gc-sections` unconditionally to Apple `ld`. Fix: adapt trial-link flags when targeting Darwin/macOS/Apple and parse Apple `ld` `", referenced from:"` undefined-symbol lines.
4. **Missing `file_read`, `file_copy`, `file_delete` re-exports (`src/app/io/file_ops.spl`)**:
   Added `export use std.io_runtime.{file_read, file_copy, file_delete}`, unblocking `app.buildrunner` and `app.bootstrap_builder`.
5. **Unbraced nominal/symbol imports (`src/lib/common/task_runner/index_v2.spl`)**:
   Braced `PureDatabase`, `DbValue`, and `builder_digest_valid_v1` imports, resolving `E-RTI-004`.
6. **Bootstrap-erased trait method returning another trait (`native_trait_registration.spl`, `native_trait_calls.spl`, `virtual_source_registration_v1.spl`)**:
   Preserved declared trait-object return type in `native_trait_declared_optional_result`, bitcast erased `i64` slot call results to `native_trait_object_type()`, and annotated `val store: VirtualSourceStoreV1 = gateway.virtual_source_store()`.
7. **Phase 3a MIR/LLVM IR lowering failures**:
   Supplied explicit `ctl_value: None` in `interpreter_binop.spl` (matching `257d8b00609` explicit-field policy), unchained `?.is_truthy()` in `interpreter_control.spl`, and added explicit local/entry type annotations in `driver_parse_shard_entry.spl`, `file_fiber_tldr_bridge_v1.spl`, `dynamic_loader.spl`, and `dynamic_adapter.spl`.
