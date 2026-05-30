# Plan: JIT-Compile Pure-Simple Software Rendering Loops (FR-COMPILER-012)

- **Date:** 2026-05-30
- **Status:** Implemented (2026-05-30)
- **Priority:** P2
- **FR:** `doc/08_tracking/feature_request/compiler_requests.md` (FR-COMPILER-012)
- **Effort:** L (2-3 weeks)

## Context

Pure-Simple per-pixel SDF rasterizers (e.g. `examples/ui/engine2d_shapes_gui.spl`)
fall back to the tree-walk interpreter because Cranelift JIT lowering fails on:

1. **`TypedInteger(0, U32)` inference** -- JIT bails with "Cannot infer type"
   when encountering `0u32`-style typed integer literals
2. **`[u32; N]` array-repeat** -- emits `rt_function_not_found` symbol that
   panics at `finalize_definitions`
3. **`.to_u32()` / `.to_f64()` / `.sqrt()` method resolution** -- some
   numeric conversion methods are unresolved in the JIT path

Tree-walk rasterization runs at hundreds-to-low-thousands px/sec, capping live
demos to 320x240 (~90s render). JIT would enable 640x480+ in seconds.

## Prerequisites and Blockers

1. **Cranelift backend infrastructure** -- exists at
   `src/compiler/70.backend/backend/cranelift_codegen_adapter.smf` and
   `src/compiler_rust/compiler/src/codegen/`
2. **Type inference pipeline** -- `TypedInteger` variant already in HIR but
   not handled in JIT lowering path
3. **Array-repeat lowering** -- `[value; count]` syntax must lower to
   Cranelift memory fill, not an unresolved runtime call
4. **No compiler FR blockers** -- this is self-contained within the codegen layer

## Phased Implementation Steps

### Phase 1: TypedInteger Inference in JIT (M)

Fix the JIT path to recognize and lower `TypedInteger(value, type_hint)` literals.

1. The JIT type-inference bail-out is in the Rust seed HIR lowering:
   `src/compiler_rust/compiler/src/hir/lower/expr/literals.rs:45` handles
   `Expr::TypedInteger(n, suffix)` but the error path is at
   `src/compiler_rust/compiler/src/hir/lower/error.rs:34` (`Cannot infer type: {0}`).
   The codegen pipeline entry is at
   `src/compiler_rust/compiler/src/pipeline/codegen.rs:526` which pattern-matches
   `Expr::TypedInteger(value, _)`. Fix the lowering so the suffix maps to a
   concrete HIR type instead of falling through to the error
2. Add a match arm for `TypedInteger(val, hint)` that maps to the concrete
   Cranelift type: `U8->i8, U16->i16, U32->i32, U64->i64, I8->i8, ...`
3. Emit the constant as `iconst` / `f64const` with the correct Cranelift type
4. Add regression test: `test/unit/compiler/jit_typed_integer_spec.spl` --
   `val x: u32 = 0u32; expect(x).to_equal(0)`

**Files to modify:** `src/compiler_rust/compiler/src/codegen/instr/core.rs`
(or wherever `TypedInteger` is matched), `src/compiler_rust/compiler/src/hir/lower/`
**Files to create:** `test/unit/compiler/jit_typed_integer_spec.spl`

### Phase 2: Array-Repeat Lowering (M)

Make `[u32; N]` / `[0u32; 640]` lower to native memory operations.

1. Identify where array-repeat expressions are lowered in the Cranelift
   codegen adapter -- currently falls through to `rt_function_not_found`
2. Implement array-repeat as: allocate `N * sizeof(T)` on stack or heap,
   emit a fill loop (or `memset` for zero-init)
3. Ensure array index assignment `buf[i] = val` lowers to a store instruction
   with bounds check
4. Ensure array index read `buf[i]` lowers to a load instruction
5. Add regression test: `test/unit/compiler/jit_array_repeat_spec.spl`

**Files to modify:** `src/compiler_rust/compiler/src/codegen/` (array lowering),
`src/compiler_rust/compiler/src/hir/lower/` (array-repeat HIR node)
**Files to create:** `test/unit/compiler/jit_array_repeat_spec.spl`

### Phase 3: Numeric Method Resolution (S)

Ensure `.to_u32()`, `.to_f64()`, `.sqrt()` resolve in JIT.

1. These methods are likely defined as runtime externs or compiler intrinsics;
   identify which are missing from the JIT symbol table
2. For conversion methods (`.to_u32()`, `.to_f64()`): emit Cranelift
   `ireduce`/`uextend`/`sextend`/`fcvt_from_sint`/`fcvt_from_uint` as
   appropriate
3. For `.sqrt()`: emit `sqrt` Cranelift instruction (IEEE 754 sqrt is a
   first-class Cranelift op)
4. Register these as known intrinsics in the JIT symbol resolver so they
   do not fall through to `rt_function_not_found`

**Files to modify:** `src/compiler_rust/compiler/src/codegen/instr/core.rs`,
symbol resolution tables in the Cranelift adapter

### Phase 4: End-to-End Validation (S)

1. Run `bin/simple run examples/ui/engine2d_shapes_gui.spl` and confirm
   it does not fall back to interpreter with type-inference errors
2. Measure render time at 640x480 -- target: under 5 seconds
3. Verify no `rt_function_not_found` panics in the JIT path
4. Run full compiler test suite to confirm no regressions

**Files to modify:** none (validation only)

## Acceptance Criteria

- [ ] `bin/simple run examples/ui/engine2d_shapes_gui.spl` JIT-compiles
      without `Cannot infer type: TypedInteger(0, U32)` interpreter fallback
- [ ] No `can't resolve symbol rt_function_not_found` panic for programs using
      `[u32; N]`, `.to_u32()`, `.to_f64()`, `.sqrt()`, and `[u32]` index ops
- [ ] High mode at 640x480+ renders in under a few seconds (vs minutes today)
- [ ] All existing compiler tests continue to pass
- [ ] New regression specs pass in both interpreter and JIT modes

## Risk Factors

- **Cranelift version compatibility (Medium):** The Cranelift API may have
  changed since initial integration; verify the `iconst`/`sqrt`/`fcvt` APIs
  match the vendored Cranelift version
- **Array heap allocation (Medium):** Large arrays like `[u32; 640*480]` may
  exceed stack limits; may need heap allocation path with `rt_alloc`
- **Method dispatch complexity (High):** If `.to_u32()` etc. go through the
  general method dispatch table rather than being intrinsics, the fix is larger
  -- may need to add a "known numeric intrinsics" fast path in JIT lowering
- **Self-hosted parity (Low):** This FR targets the Rust seed JIT path;
  self-hosted compiler parity is a separate concern
