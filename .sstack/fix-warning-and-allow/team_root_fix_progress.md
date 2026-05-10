# result_large_err Root Fix — Progress Report

## Summary

Eliminated all `clippy::result_large_err` warnings (was 1512 instances) by shrinking
`CompileError` variants via heap-boxing.

## Changes

### New type: `ContextualError` (error.rs)
Boxed payload for the 6 rich-context variants so `ErrorContext` (~150 bytes) lives on the heap.

### Variants converted (6)
- `IoWithContext { message, context }` → `IoWithContext(Box<ContextualError>)`
- `ParseWithContext { message, context }` → `ParseWithContext(Box<ContextualError>)`
- `SemanticWithContext { message, context }` → `SemanticWithContext(Box<ContextualError>)`
- `CodegenWithContext { message, context }` → `CodegenWithContext(Box<ContextualError>)`
- `LintWithContext { message, context }` → `LintWithContext(Box<ContextualError>)`
- `RuntimeWithContext { message, context }` → `RuntimeWithContext(Box<ContextualError>)`

### Also boxed: `TryError(Value)` → `TryError(Box<Value>)`
`Value` has large variants (Lambda with Box<Expr>+Arc<Env>, BlockClosure with Vec<Node>+Arc<Env>)
making it significantly larger than 128 bytes.

### Also fixed: `declare_uniform_i64_import` in codegen/instr/helpers.rs
Returns `cranelift_module::ModuleError` (third-party, 136 bytes). Changed return type to
`Result<FuncId, Box<cranelift_module::ModuleError>>`.

## Files touched (9)
1. `src/compiler_rust/compiler/src/error.rs` — definition + 6 factory methods + context/message/severity match arms
2. `src/compiler_rust/compiler/src/pipeline/execution.rs` — 1 construction + match site
3. `src/compiler_rust/compiler/src/pipeline/mod.rs` — 2 test pattern-match sites
4. `src/compiler_rust/compiler/src/interpreter/expr.rs` — 4 TryError construction sites
5. `src/compiler_rust/compiler/src/interpreter_call/core/macros.rs` — 1 TryError match
6. `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs` — 1 TryError match
7. `src/compiler_rust/compiler/src/interpreter_call/core/class_instantiation.rs` — 1 TryError match
8. `src/compiler_rust/compiler/src/interpreter_method/special/types.rs` — 1 TryError match
9. `src/compiler_rust/compiler/src/interpreter_method/special/execution.rs` — 2 TryError matches
10. `src/compiler_rust/compiler/src/codegen/instr/helpers.rs` — ModuleError boxing
11. `src/compiler_rust/compiler/src/lib.rs` — removed `#![allow(clippy::result_large_err)]`
12. `src/compiler_rust/Cargo.toml` — removed `result_large_err = { level = "allow", priority = 1 }`

## Counts
- Constructor sites updated: 11 (6 WithContext factory methods + 1 contract_violation + 4 TryError)
- Pattern-match sites updated: 12 (6 context() + 6 message() + 2 severity + 2 pipeline tests + 7 TryError + 1 execution.rs)
- Files with suppressions removed: 2

## Final warning count
`cargo clippy --no-deps -p simple-compiler 2>&1 | grep -c 'result_large_err'` → **0**

## Commit hashes
- Stage 1 (refactor): `f70690e482db` — refactor(error): box ErrorContext in CompileError variants to fix result_large_err
- Stage 2 (suppressions): `e71662cc52e7` — chore(clippy): remove result_large_err allow now that root cause is fixed
