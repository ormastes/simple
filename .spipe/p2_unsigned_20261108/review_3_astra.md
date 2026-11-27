# Independent Astra source review — PR #7847

**STATUS: FAIL**

- BASE: `0247364fa1ad6b5818b24da451034ca6cf507e42`
- HEAD: `9932323be75d2d44bc37ba1c078c4e4f6bab6409`
- Worktree: `/tmp/simple-p2-narrow-unsigned-mir-width-20261108`
- Scope: independent source review; no compiler execution, tests, builds, GitHub writes, or repository edits. Findings below are deductions from the immutable Git objects, not executed reproductions.

Two new silent-miscompile paths block source acceptance. Neither depends on unsigned arithmetic overflow, literal-wrapping policy, floating conversion, or the documented legacy-PHI residual. All line references refer to HEAD.

## P1-1 — A declared i64 binding hides the narrow producer from MIR promotion

**Changed producer:** `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:5813-5820` now makes the result of U8+U8 an actual U8 local. The common-operand repair at `:5901-5909` uses registered MIR types, so it does not cover a binding whose registered type is I64 but whose LLVM definition becomes i8.

Concrete source shape:

```simple
fn bound_after_binding(a: u8, b: u8, bound: i64) -> bool:
    val wide: i64 = a + b
    wide < bound
```

For `(100, 100, 256)`, the unchanged arithmetic value is 200. BASE compares i64 200 with i64 256 and returns true. At HEAD, the source path emits an i8 comparison against the truncated bound 0 and returns false.

Caller/control evidence:

1. HIR preserves the annotation and ordinary Binary initializer separately; it does not insert an integer widening cast (`20.hir/hir_lowering/statements.spl:902-919`).
2. `lower_expr_for_slot` falls through to ordinary expression lowering for this i64 slot (`50.mir/mir_lowering_stmts.spl:2755-2856`). The Let path casts only narrow-integer or floating annotations (`:1435-1454`), so i64 is excluded. It creates an I64 binding (`:1548-1601`, `:1672`) and emits Copy from the U8 initializer (`:1798`).
3. Reading the variable returns that registered local directly (`expr_dispatch.spl:6443-6449`). `local_mir_type_of` reads the builder's declared type (`mir_lowering_stmts.spl:547-553`). Thus the outer comparison sees I64/I64 and does not enter the new narrow-unsigned promotion.
4. LLVM `translate_copy_move` defines the destination at the **source** physical type and replaces its unsigned metadata (`70.backend/backend/_MirToLlvm/core_codegen.spl:2366-2370`, `:2401-2419`, `:2432-2433`). `wide` therefore becomes i8, unsigned.
5. LLVM Lt compares at the actual left operand's width and converts the right operand to it (`core_codegen.spl:2588-2594`). I64 bound 256 is truncated to i8 0.
6. Canonical typed-alloca SSA does not rescue a single-definition, same-block binding: cross-block analysis returns empty for one block (`60.mir_opt/mir_opt/var_reassign_ssa.spl:1459-1464`), and no-slotted-locals is a no-op (`:1879-1880`). A separately slotted return local does not widen this earlier comparison.

The new fixture's `implicit_let8` only returns the binding (`test/fixtures/compiler/same_width_unsigned_binop/main.spl:29-31`). The already unsigned-aware return conversion makes that check pass without checking later arithmetic/comparison consumers.

**Repair direction:** materialize the declared numeric conversion at the binding boundary, or otherwise preserve a truthful declared/physical type contract. Add a real lowered-function check for the binding followed by `<`, `==`, and a negative signed peer. The direct `a+b < bound` positive control must remain valid.

## P1-2 — Excluding Is/IsNot reopens the truncating-comparison path on this rebased base

**Changed gate:** `expr_dispatch.spl:5898-5903` excludes Is and IsNot. The earlier review's premise that generic Is maps to Add is stale for the reviewed BASE and HEAD: both map Is to `MirBinOp.Eq` and IsNot to `MirBinOp.Ne` (`50.mir/_MirLoweringExpr/switch_operators_calls.spl:2183-2184`). The nearby comment at `expr_dispatch.spl:4848-4849` does not match that executable owner.

Concrete source shapes are `(a + b) is bound` and `(a + b) is not bound`, with `a=b=100u8` and `bound=456i64`.

- HIR explicitly preserves value-versus-value Is as Binary; only a RHS naming a type takes the TypeTest route (`20.hir/hir_lowering/_Expressions/expression_core.spl:1038-1060`). A bound variable also bypasses the MIR qualified-enum Field special case (`expr_dispatch.spl:4852-4894`).
- The inner sum becomes U8. Is/IsNot are absent from both `comparison` (`:5833-5835`) and the common-integer gate, so the outer operands remain U8/I64.
- `equality_compare_type` selects the left type except for its Bool exception (`core_codegen.spl:1696-1709`); Eq/Ne then convert the RHS to it (`:2573-2586`). Thus 456 truncates to 200.
- BASE returns false/true for Is/IsNot; HEAD returns true/false. The reverse operand order is also unsafe: a signed-default widening of the U8 sum 200 produces -56 in a wide-left comparison.

**Repair direction:** preserve the existing supported numeric value-comparison behavior with lossless operand coercion, without changing type-test or enum-pattern handling. Include both operators and operand orders in MIR/backend/native regressions. Explicitly excluding these consumers from the feature does not make their new regression pre-existing.

## Other reviewed contracts and prior findings

- Same-width host Add/Sub/Mul retain U8/U16/U32 in MIR. LLVM emits width-specific arithmetic without signed-overflow flags for these operands; Cranelift canonicalizes unsigned narrow results into its uniform i64 representation (`cranelift_codegen_adapter.spl:637-647`, `:2067-2084`). Scalar slots have an eight-byte floor (`:483-502`).
- Known-type presence gating, six ordinary comparison operators, negative-peer common carriers, and the existing operand-width unary lowering address the prior source findings. Corrected unary expectations 56/55 match `expr_dispatch.spl:6818-6826`.
- The changed call, intrinsic, global, GEP, offset, exception and verbatim-field paths pass actual unsigned metadata. `value_as_type_signed(..., false)` retains the previous conversion behavior; the verbatim field helper still avoids the sticky value map. Existing three-argument signed field-helper callers retain their default false.
- The new IR specs own a positive builder handle and function/CFG context. Their absence of executions remains explicit. They do not cover P1-1 or P1-2.
- Canonical constant folding is inactive; the reviewed driver uses the registered optimization pipeline, not the legacy untyped folding engine. Canonical LLVM branch reassignment uses typed-alloca SSA first. No speculative PHI structural repair is part of this diff.
- Tracking changes retain verification-pending status and historical failed reviews. The old cycle-3 handoff identifies an earlier base/head; the newer draft handoff and immutable diff establish the identities above.

## Qualification limits

No P0 found. No additional independent P2 finding is required for this disposition. This is **not** runtime qualification or permission to merge. The 42-check LLVM/Cranelift/interpreter differential, MIR/IR specs, wrong-expectation negative control, compiler/lib/MCP/LSP gates, native smokes, fixed-point and HIR-cache-hash checks remain **UNRUN**. Static/push gates and pending CI are not substitutes. Literal wrapping, broader mixed/U64 policies, floating call conversion and legacy mixed-width PHI behavior remain explicitly unqualified. Fix the two source regressions before another source acceptance decision.
