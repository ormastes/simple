# C1+C2 Blocker: Spec Test Compile Error (Missing InstBuilder Import)

**Date:** 2026-04-28
**Cluster:** C1+C2
**Status:** PARTIAL BLOCKER — spec test cannot compile as written

## Summary

The spec test at `src/compiler_rust/compiler/tests/call_runtime_helpers.rs` has a
missing `use cranelift_codegen::ir::InstBuilder;` import at line 266-267 in the
`c2_declare_uniform_i64_import_idempotent` test body:

```rust
let zero = builder.ins().iconst(types::I64, 0);  // line 266
builder.ins().return_(&[zero]);                   // line 267
```

Both `iconst` and `return_` are methods on the `InstBuilder` trait, which must be
explicitly imported in Rust. The spec test imports `cranelift_codegen::ir::types`
but not `cranelift_codegen::ir::InstBuilder`.

## Root Cause

The spec test was authored as architecture documentation (Phase 2) without being
compiled/tested. It contains a missing trait import.

## What Was Fixed

The Phase 5 engineer fixed all other spec test compile errors:

| Error | Fix Applied |
|-------|------------|
| E0433: `cranelift_native` not found | Added `cranelift-native = "0.116"` to `[dev-dependencies]` in `Cargo.toml` |
| E0599: `new_for_test` not found | Added `InstrContext::new_for_test` with `#[doc(hidden)] pub` — takes `&HashMap<String, FuncId>` (matching the test's actual type) |
| E0603: helpers are private | Changed all 6 helpers from `pub(crate)` to `pub` |
| E0308: type mismatch in `new_for_test` | Changed parameter to `&HashMap<String, FuncId>` with internal `Box::leak` conversion |

## What Cannot Be Fixed Without Editing the Spec

Two errors remain at `call_runtime_helpers.rs:266-267`:
```
error[E0599]: no method named `iconst` found for struct `FuncInstBuilder<'short, 'long>` in the current scope
error[E0599]: no method named `return_` found for struct `FuncInstBuilder<'short, 'long>` in the current scope
```

These require adding `use cranelift_codegen::ir::InstBuilder;` to the spec test file.

## Recommended Fix (requires spec edit)

Add to `call_runtime_helpers.rs` at the top of the `c2_declare_uniform_i64_import_idempotent` test:
```rust
use cranelift_codegen::ir::InstBuilder;
```
Or at line 207 inside the test function block:
```rust
use cranelift_codegen::ir::InstBuilder;
```

This is a one-line fix to the spec test. Phase 5 engineer cannot apply it per
instructions ("Do NOT edit the spec test").

## What C1+C2 Delivered Despite the Blocker

- 6 helpers added to `helpers.rs` (C1: 5 call_runtime_N + C2: 1 declare_uniform_i64_import)
- `InstrContext::new_for_test` added to `mod.rs`
- `cranelift-native` added to `[dev-dependencies]`
- All non-spec tests pass (cargo build clean)
- C1b site rewrites NOT committed (commit gate: spec must pass per instructions)

## Impact

Per mission instructions: "If blocked at any step: write to `.sstack/semantic-dup-removal/C_blocker.md`
and stop." The spec compile failure is the blocker. C1b rewrites (74 sites) and C2 call-site
rewrites (4 sites) were NOT applied to avoid a commit on a failing spec.

## Mitigation Options

1. Allow Phase 5 engineer to apply one-line fix to spec test (recommended)
2. Add `pub use cranelift_codegen::ir::InstBuilder` to `simple_compiler::codegen::instr`
   module — but this doesn't help because the spec uses a specific import `{InstrContext, InstrResult}`,
   not a glob. Traits must be explicitly in scope.
3. Restructure the `c2_declare_uniform_i64_import_idempotent` test to avoid using
   `builder.ins()` methods directly (e.g., use `compile_ok()` instead) — requires spec edit.
