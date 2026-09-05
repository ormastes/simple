# Stage-2 tool codegen drops the `rt_panic` runtime root

**Status:** Fix diagnostic-confirmed; pure-Simple admission remains blocked.

## Failure

The admitted pure-Simple Stage-2 compiler aborts before object emission when
native-building either MCP tool from the current compiler/app/lib closure:

```text
missing runtime fn 'rt_panic' in AssistantStore.new
missing runtime fn 'rt_panic' in simple_log_options_defaults
```

MCP failed after 2.79 seconds at 167,100 KiB peak RSS; Simple LSP MCP failed
after 1.92 seconds at 163,840 KiB. Both exited 134 and produced no executable.
The frozen runtime archives export `rt_panic`, so this is codegen registration,
not a linker-provider absence.

## Root cause and fix

Generated struct-allocation failure paths call `rt_panic`, but
`runtime_symbol_is_codegen_root` did not retain it when source MIR contained no
explicit panic call. `src/compiler_rust/compiler/src/codegen/common_backend.rs`
now classifies `rt_panic` as a synthesized codegen root. Its adjacent Rust unit
assertion pins the root.

## Evidence boundary

The failing Stage-2 authority predates the fix. A current Rust diagnostic driver
rebuilt successfully, the exact `synthesized_runtime_symbols_are_retained` unit
test passed (1/1), and the native-build CLI closure linked. MCP then progressed
past every former `rt_panic` failure and reached the separate
`rt_char_from_code` provider mismatch. This confirms the diagnosis without
constituting admission evidence. Closure of this record still requires a newly
admitted pure-Simple producer to build both tools with fallback disabled and
pass native protocol smoke.

Retained logs:

- `build/native_probe/stage2-tools/mcp/log/native-build.log`
- `build/native_probe/stage2-tools/simple-lsp-mcp/log/native-build.log`
- `build/native_probe/current-rust-seed/log/common-backend-rt-panic-root-test.log`
- `build/native_probe/current-rust-seed/mcp-cycle2/log/native-build.log`
