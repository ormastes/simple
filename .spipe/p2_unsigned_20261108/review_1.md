# Independent Review: same-width unsigned MIR arithmetic

**STATUS: FAIL**

- **BASE:** `2e3087b949e106ed78a25a0d08eca476c5b4041e`
- **HEAD:** `0ac9c5ef54590aeba3addfcb726de656374cd148`

This is a source review only. I invoked no tools and executed nothing. Nothing here counts as runtime qualification, and the MIR spec and native fixture remain **UNRUN**.

## What holds up in the source

- **Scope is narrow.** The new block at `expr_dispatch.spl:5760-5768` applies only when all of these are true:
  - the target is not GPU (`current_gpu_kernel_target == ""`);
  - the operator is `Add`, `Sub` or `Mul`;
  - both MIR local kinds are the same U8, U16 or U32.
- **Earlier checks are unaffected.** The float override at 5719-5723 cannot fire for U8/U16/U32 operands. The Vulkan U32 override at 5785-5794 is gated off.
- **LLVM lowering looks right.** In `translate_binop` (`core_codegen.spl:2470-2514`), a U8 destination gives `ty = "i8"`. `value_as_type_signed` then does no conversion, and `bin_unsigned` selects plain `add`/`sub`/`mul` without `nsw`. The destination's unsigned bit is set from its MIR type at `core_codegen.spl:882`, so an explicit `as i64` should zero-extend.
- **Cranelift lowering looks right.** In `cranelift_codegen_adapter.spl:637-643`, `cl_canonicalize_unsigned_narrow` now fires for the U8/U16/U32 destination (`ireduce` then `uextend`). Before this patch it never fired because the destination was I64.
- **Callers.** There are only two production callers, `expr_dispatch.spl:5992` and `:6719`, and both forward directly. The census is complete for direct calls.
- **Fixture arithmetic.** I hand-checked eight of the nine expected values. `mul32 = 1321730048` matches the existing interpreter spec value; I did not recompute it.

## Findings

### P1-1: Comparing a narrowed arithmetic result with an i64 value now truncates the i64, a new silent miscompile

**Where:** the new block at `expr_dispatch.spl:5760-5768`, interacting with the existing narrowing at `expr_dispatch.spl:5844-5847`.

**Caller chain:**
1. The outer comparison enters `lower_binary_expr`.
2. At line 4944 it calls `self.lower_expr(left)`.
3. That reaches the inner `lower_binary_expr` through line 5992 or 6719.
4. The inner call now returns a U8/U16/U32 local.
5. In the outer call, `left_narrow_int` is true, and an unsuffixed literal is an I64 local, so `right_i64` is true.
6. Line 5845 therefore casts the **i64 side down** to the narrow type.

**Example:** `val a: u8 = 100; val b: u8 = 100; a + b < 256`

| Lane | Computation | Result |
|---|---|---|
| Interpreter | `200 < 256` | true |
| Native before this patch | I64 result, `200 < 256` | true |
| Native after this patch | `200u8 < (256 → u8 = 0)` | **false** |

- No overflow is involved, so this breaks code that was previously correct.
- The same mechanism makes `a + b == 256` true on native for `a + b == 0` wrapped values, while the interpreter says false.
- It applies to U16/U32 bounds checks too, e.g. `off + len <= 65536`, and to the mirrored `n < a + b` case at line 5846.
- The truncating comparison narrowing already existed for plain narrow locals. This patch is what newly routes arithmetic results into it.

**Suggested fix:** for a narrow-unsigned versus i64 comparison, widen the narrow side with an unsigned-aware cast instead of truncating. Alternatively, narrow only when the i64 side is an `IntLit` within range.

**Tests to add:** spec and fixture cases such as `(100u8 + 100u8) < 256 == true` and `(a + b) == 256 == false`.

### P2-1: The spec pins known-defective behavior as expected

- `same_width_unsigned_binop_spec.spl:53` asserts that U64 + U64 gives `MirTypeKind.I64`.
- That I64 typing drops the unsigned bit. Downstream `>>` then becomes `ashr` and `Div` becomes signed when the other operand is not U64 (`core_codegen.spl:2520`, `:2564-2572`).
- Line 60 likewise pins CUDA U8 + U8 as I64.
- These lines are characterization, not contract, and a later correct fix would fail them.
- **Fix:** assert only that the result is "not narrowed to U8/U16/U32", or label these lines explicitly as current-behavior characterization.

### P2-2: Neither regression covers implicit widening

- The fixture always uses an explicit `as i64` (fixture lines 5-13). That avoids the implicit consumers that now receive i8/i16/i32 values on LLVM:
  - an implicit return to `-> i64`;
  - `val x: i64 = a + b`;
  - call arguments, especially `(...)`-declared non-extern callees, per `mir_types.spl:64-70`;
  - array index and GEP use;
  - struct field stores;
  - string interpolation and `print`.
- If any of these widens through sign-extension (`value_as_type`) instead of `value_as_type_signed(..., unsigned)`, then a sum of 128 or more becomes negative. That was previously correct.
- Neither test exercises this, and I cannot confirm it from the supplied context.

### P2-3: The spec's import surface is unproven

- The working sibling spec `unsigned_conversion_result_spec.spl:7-8` imports `MirLowering` and `MirTypeKind` explicitly from `mir_lowering` and `mir_types`.
- The new spec instead relies on `compiler.mir.mir.*` re-exporting them. `mir.spl` only has `use` glob statements, and `expr_dispatch.spl:52` warns that "a glob is not an import-origin for surface projection".
- `Span.empty()` is not shown anywhere in context.
- Even if the spec runs, it may fail at resolution rather than test anything.

### P2-4: The bug record's status is inconsistent

- `interp_uint_mixed_int_arith_diverges_from_jit_2026-11-06.md:3` still reads `Status: OPEN - the premise ... does not hold; no interpreter change made`.
- The new section at line 88 says "Keep status `fix-implemented-verification-pending`", which is a status the file never carries.
- **Fix:** update the header to the canonical waiting_verify / verification-pending state, still without any fixed claim.

## Limitations and context needed before a PASS

1. **Implicit-widening owners:** LLVM `translate_cast`, `translate_store`, the return lowering and `translate_call` argument coercion (`_MirToLlvm/core_codegen.spl`). Also the MIR let/assign/return coercion (`mir_lowering_stmts.spl`) and call-argument coercion (`switch_operators_calls.spl`). These would resolve P2-2.
2. **MIR optimization passes** that fold or simplify `BinOp` (const-fold, SCCP, instcombine-like passes, inliner). Host BinOps with U8/U16/U32 destinations are a new shape, and folding without a width wrap would emit `Const(260, U8)`. Cranelift would not canonicalize that.
3. **Cranelift slot allocation** (where `slot_map` is built) and `cl_translate_binop`. This confirms that the raw 64-bit `cranelift_store` at `cranelift_codegen_adapter.spl:645-647` cannot overrun a narrow slot. Note that `UnaryOp` uses `store_local_result` instead.
4. **`find_local`'s definition.** This confirms that `lowering.local_map[101] = ...` (spec lines 27-28) is the lookup the Var pre-dispatch at line 6381 actually uses.
5. **Self-host impact:** a census of U8/U16/U32 `+ - *` sites in `src/compiler/**` and the stage-N fixed-point and HIR-cache-hash comparison. The native-built compiler's own narrow-unsigned arithmetic now changes behavior.
6. **Runtime gates:** every runtime gate listed in the bug record is unexecuted, including the MIR spec, LLVM and Cranelift fixture execution, and the wrong-expectation negative control. No runtime PASS can be inferred.

Original response SHA256: `a76e69832f127db0c4451015dea0b31cece5b4811e9106a0fa8daea9f8cc58b0`. This FAIL history is retained; no later source PASS is claimed.
