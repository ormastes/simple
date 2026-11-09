# Independent Opus Review: narrow-unsigned MIR width and LLVM consumers (cycle 2)

**STATUS: FAIL**

- **Reviewed BASE:** `2e3087b949e106ed78a25a0d08eca476c5b4041e`
- **Reviewed HEAD:** `09341cd173446bbe0e60a40cb385aa591fa9ddce`

This is a source-only review of the supplied patch and context. I invoked no tools and executed nothing. The MIR spec, the backend spec and the native fixture are all **UNRUN**, and nothing here implies runtime, fixed-point, cache-hash or self-host qualification.

## Prior-cycle findings: status at this HEAD

| Prior finding | Status | Evidence |
|---|---|---|
| P1-1: a narrow result compared with an i64 bound truncated the bound | **Resolved in source** | `expr_dispatch.spl:5874-5885` now promotes both operands through `mir_narrow_unsigned_integer_common_type` (`:208-234`) before the legacy truncating `elif` at `:5886-5889`. For `a + b < 256`, U8 is cast to I64 (zero-extended by `llvm_cast_impl`, `aggregate_intrinsics.spl:467`), the cast destination is marked signed (`:456`), and LLVM emits `slt` on i64. Negative peers sign-extend. |
| P2-1: spec pinned U64→I64 and CUDA→I64 | **Resolved** | Those assertions are gone from `same_width_unsigned_binop_spec.spl`. |
| P2-2: no implicit-widening coverage | **Largely addressed** | The fixture adds return/let/call/field/index/text/global/branch/unary/match consumers. The backend threads signedness at call (3 routes), verbatim field, GEP, Offset, Neg/BitNot, Switch, Throw/Resume, PHI and both StoreGlobal routes. |
| P2-3: spec import surface | **Resolved** | Explicit owner imports are used. `find_local` (`mir_lowering_types.spl:984-1000`) falls back to `local_map`. |
| P2-4: bug-record status | **Resolved** | The header now reads `fix-implemented-verification-pending`. |

### What else checks out in the source

- **Caller census:** `lower_binary_expr` has exactly two production callers (`expr_dispatch.spl:6034`, `:6761`), and both forward directly.
- **Verbatim-field caller census:** the census is complete. Existing signed callers keep the default `false`, so `llvm_struct_word_store_width_spec.spl` still expects `sext`.
- **Backend changes are strictly additive:** `value_as_type_signed(..., false)` is equivalent to `value_as_type`. Behavior changes only where `unsigned_locals` is true.
- **Cranelift:** stack slots are a uniform 8 bytes (`cranelift_codegen_adapter.spl:494-502`), so the raw 64-bit BinOp store cannot overrun. `cl_canonicalize_unsigned_narrow` now fires for the new U8/U16/U32 destinations.
- **Optimizer:** the canonical `const_fold` is an inactive skeleton (`const_fold.spl:18-26`). The legacy untyped `mir_fold_binop` engine is not called from the driver, per the supplied census.
- **Fixture arithmetic:** I hand-verified the expected values for checks 1-8, 10-37 and 40 under the patch's own native policy. Check 9 matches the existing pinned interpreter value.

## Findings

### P1-1: Fixture checks 38 and 39 accept a native-versus-interpreter divergence for unary operators on narrow unsigned values

**Where:**
- Fixture: `test/fixtures/compiler/same_width_unsigned_binop/main.spl:66-67`, asserted at `:111-112`. These expect `-(a+b) == -200` and `~(a+b) == -201` for a U8 sum of 200.
- Backend owner: `core_codegen.spl:2643` and `:2665` zero-extend a U8 operand into an i64 destination, then negate or invert at 64 bits.
- Backend spec: `narrow_unsigned_consumer_widening_spec.spl:165-169` pins that widening.

**Contract it contradicts:**
- The interpreter's documented semantics are in `u32_wrap_arith_spec.spl:45-50` and `:56`: "Add/Sub/Mul/**Neg** apply `wrapping_*` at the operand width when at least one side is `Value::UInt`; bitwise/shift ops preserve UInt-ness". The spec also lists "u32 negation wrap".
- Under that rule the interpreter yields `-(200u8) = 56` and `~(200u8) = 55`.
- The bug being fixed is the interpreter/native divergence for narrow unsigned arithmetic. These two checks make native i64 unary semantics a required admission result ("exact 40-check stdout"), which accepts that divergence.

**Outcome depends on unary MIR result typing, which was not supplied:**
- If the unary destination is I64, as the comment at `core_codegen.spl:2652-2654` suggests, the patch produces -200/-201. That diverges from the interpreter and the fixture passes.
- If unary lowering keeps the operand's narrow type, as Cranelift's comment about U32 `~x` at `cranelift_codegen_adapter.spl:2071-2074` implies can happen, the result is 56/55 and the fixture fails at check 38.

**Fix:** decide unary semantics explicitly and then do one of the following:
- type Neg/BitNot of a narrow-unsigned operand at operand width in MIR, matching the interpreter, and update the checks to 56/55; or
- drop checks 38-39 and record unary as an open residual.

Either way, add an interpreter run of the same fixture as a differential gate.

### P2-1: The backend call test passes `ir_handle = 0`, so the call line bypasses the inspected builder

**Where:** `narrow_unsigned_consumer_widening_spec.spl:34` calls `translate_call_at([instruction], 0, 0)`, which passes index 0 and **ir_handle 0**.

**Why it fails:**
- In `translate_call_at`, the no-destination path checks `if ir_handle >= 0:` (`core_codegen.spl:2866-2868`). With handle 0 it sends `call void @wide(...)` to `_sffi_string_builder_push(0, ...)` instead of `self.builder`.
- The assertion `expect(ir).to_contain("call void")` (`:124`) therefore cannot pass for the "instruction" route. Handle 0 may also be invalid at runtime.
- The `zext` assertion still passes, because the conversion is emitted through `self.builder`.

**Fix:** pass `-1`, as the global-store test already does (`:68`).

### P2-2: "Unknown operands remain unchanged" is not what the code does

**Where:**
- Bug doc `:70-71` says "tagged-runtime/unknown operands ... remain unchanged".
- In code, `left_binop_type`/`right_binop_type` default to `MirType.i64()` when `local_mir_type_of` is nil (`expr_dispatch.spl:5765-5766`). The common-type helper then treats them as integers and emits a `Cast` to I64 (`:5877-5885`).

**Effect:** previously such an operand reached no cast at all, because the `left_i64`/`right_i64` flags were set only when a type was present. Now an untyped local paired with a narrow-unsigned operand gets an I64 cast. If that local is pointer-flavored, LLVM selects `ptrtoint` or a conversion error.

**Fix:** gate the promotion on explicit type presence, or correct the documentation.

### P2-3: The bug record contradicts itself on promotion policy

**Where:** bug doc `:64-68` introduces a new common-carrier promotion for all integer `+ - * / % ** & | ^ << >>` and comparisons when a narrow-unsigned operand is involved. Line `:85` then says "No new general promotion or overflow policy is selected here."

**Why it matters:**
- The context says root approved this policy, so it should be recorded as that approved decision, not denied.
- Checks 15, 16, 18 and 29-32 (negative peers in compare/div/rem) are native policy choices. They have not been shown to match interpreter results; its UInt-wins and literal-sensitive rules make that uncertain.
- The admission list (`:100-104`) has no interpreter differential, which this bug class requires.

### P2-4: Is/IsNot promotion is pinned by tests although the operator lowering is known to be mis-mapped

**Where:**
- `integer_numeric_op` includes `Is | IsNot` (`expr_dispatch.spl:5875`), and the spec iterates 8 operators including both (`same_width_unsigned_binop_spec.spl:89`).
- The comment at `expr_dispatch.spl:4829-4830` says the generic `Is` fallback maps to `MirBinOp.Add`.
- The doc claims "all six comparison operators".

**Fix:** either exclude Is/IsNot, or record that the spec characterizes current behavior rather than defining a contract.

## Limitations and specific context needed

1. **Unary result typing:** the `HirExprKind.Unary` arm in `expr_dispatch.spl`, which decides P1-1's concrete outcome.
2. **Comparison producers that bypass `lower_binary_expr`:**
   - The backend's ordered comparisons still compare at the **left operand's** type and truncate a wider right side (`core_codegen.spl:2588-2615`). Eq/Ne still use signed `value_as_type` through `equality_compare_type`, whose body was not supplied.
   - Narrow arithmetic results now reach any MIR producer that emits comparisons directly. Fixture checks 27 and 40 depend on this.
   - Owners needed: `emit_bounds_check_for_index`, match-case pattern lowering, range/for lowering, `equality_compare_type`, and `lower_compound_combine`. The last is needed to tell whether `x += y` on u8 shares the new rule or remains an undeclared residual.
3. **`HirBinOp` definition** (`compiler/20.hir/hir_operators.spl`): confirms that `BitAnd/BitOr/BitXor/Shl/Shr/Mod/Is/IsNot` are real variants. A bare unknown name in the `match` at `:5874-5876` could otherwise bind as a catch-all.
4. **Cranelift call-argument coercion** for an integer argument passed to an f64 parameter (check 34). Also whether the frontend type checker accepts implicit u8→f64 and u8→i64 at all.
5. **Self-host impact:** the static census (1185 rows across 288 files) shows wide use of u8/u16/u32 in the compiler. Same-width `+ - *` now wraps in the native-built compiler, and the narrow compare semantics have changed. Fixed-point, HIR-cache-hash parity and self-host native qualification were not executed.
6. **Runtime gates:** none of the gates listed in the bug record were executed (MIR spec, backend spec, LLVM and Cranelift fixture execution, wrong-expectation negative control, interpreter differential). No runtime PASS is implied or available.

Original response SHA256: `d2ce0432277dd0083a28c89ad8e6afb5e0930ad82510c0450eb87f5a9c9f5156`. This FAIL history is retained; no later source PASS is claimed.
