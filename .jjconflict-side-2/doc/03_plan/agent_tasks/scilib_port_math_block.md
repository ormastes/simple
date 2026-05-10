# scilib_port_math_block.md — Math Block v1 Extensions TODO

**Area:** `math_block`  
**Status:** Phase 4 (spec/impl planning)  
**Date:** 2026-04-27  
**Depends on:** T-NDARRAY-* (NDArray core), T-BLAS-* (BLAS shim), T-LAPACK-* (LAPACK shim)  
**Disjoint from:** ndarray, blas, lapack, cuda_fortran, df, ml, perf_sugar areas  
**Locks honoured:** OQ-A (runtime dispatch v1, HIR-lift v2); architect anti-pattern #2 (df NEVER in math{})  
**Source files touched (v1):** `src/compiler_rust/compiler/src/blocks/math/lexer.rs`, `parser.rs`, `ast.rs`, `eval/mod.rs`, `tensor/indexing.rs`, `rendering/`

---

## Dependency Summary

| Sibling area | Required for | Min status before starting |
|---|---|---|
| T-NDARRAY-01 (NDArray<T> struct + MockBackend) | Slice eval, inv/solve result type | NDArray<T> struct merged |
| T-BLAS-01 (BLAS shim symbols) | `@` eval via matmul backend | mock symbols in `libspl_cublas_mock.so` |
| T-LAPACK-01 (LAPACK shim symbols) | `inv` / `solve` eval arms | `rt_lapack_dgetrf`, `rt_lapack_dgetri`, `rt_lapack_dgesv` in mock |
| T-PERF-SUGAR-001 (rt_f64_array_alloc) | Intermediate tensor alloc in eval | must be `fixed` (hard gate inherited from ndarray) |

---

## Anti-Patterns (do NOT propose)

1. **Do not put DataFrame ops in `math{}`** — string-keyed indexing is fundamentally incompatible with `MathExpr`. `df['col']` and `groupby` stay in pure Simple method calls.
2. **Do not require HIR-lift for v1** — all changes in v1 are runtime string-interp extensions only. The `math{}` block remains a payload-string interpreter; no grammar-level Simple parser changes.
3. **Do not use `--mode=native` or `--mode=smf` to green specs** — all specs must pass via `bin/simple test` in interpreter mode with `SIMPLE_BLAS_BACKEND=mock`.
4. **Do not convert TODOs to NOTEs** — implement or delete.
5. **Do not use `skip()`** — all v1 spec scenarios must be active and passing.

---

## v1 Tasks (runtime string-interp extensions)

### T-MATHBLOCK-01 — Lexer: add `@` token (matmul)

**Scope:** `blocks/math/lexer.rs`  
**Estimate:** 0.5 day  
**Deps:** none (compiler-only)

Add `MathToken::At` for the `@` character. Assign operator precedence between `Mul` and `Pow` (i.e., above `+`/`-`, below `^`). Verify the token does not collide with any existing math lexer token — the math lexer currently uses `..` for Range; `@` is free. Add a lexer unit test: `assert lex("A @ B")` produces `[Ident("A"), At, Ident("B")]`.

**Risk:** Low. Single character addition to a closed token enum.

---

### T-MATHBLOCK-02 — Lexer: add `:` slice token

**Scope:** `blocks/math/lexer.rs`  
**Estimate:** 0.5 day  
**Deps:** none (compiler-only)

Add `MathToken::Colon` for `:`. Confirm the math lexer uses `..` (not `:`) as the range token for binder forms (`Sum/Prod/Integral`), so `:` is unambiguously free. Add a lexer unit test: `assert lex("A[1:3]")` produces `[Ident("A"), LBracket, Int(1), Colon, Int(3), RBracket]`.

**Risk:** Low. But the developer must grep `blocks/math/lexer.rs` for any existing `:` handling before adding to avoid silent precedence collisions.

---

### T-MATHBLOCK-03 — AST: add `MatMul` variant

**Scope:** `blocks/math/ast.rs`  
**Estimate:** 0.5 day  
**Deps:** T-MATHBLOCK-01 (token must exist before parser can produce the node)

Add `MatMul(Box<MathExpr>, Box<MathExpr>)` to the `MathExpr` enum. Update `display` / `Debug` impls. No change to eval yet (handled in T-MATHBLOCK-06).

**Risk:** Low.

---

### T-MATHBLOCK-04 — AST: add `Slice` node and `SliceRange` type

**Scope:** `blocks/math/ast.rs`  
**Estimate:** 0.5 day  
**Deps:** T-MATHBLOCK-02

Add:
```
struct SliceRange { start: Option<MathExpr>, stop: Option<MathExpr> }
Slice { base: Box<MathExpr>, ranges: Vec<SliceRange> }
```
to `MathExpr`. Update `display` / `Debug` impls. `ranges` length equals the number of subscript axes; `..` (all-elements) is represented as `SliceRange { start: None, stop: None }`.

**Risk:** Low for the data structure. The parser side (T-MATHBLOCK-05) carries the medium risk.

---

### T-MATHBLOCK-05 — Parser: `@` infix, `A[i:j,k]` subscript, `.method` postfix normalisation

**Scope:** `blocks/math/parser.rs`  
**Estimate:** 2 days  
**Deps:** T-MATHBLOCK-01, T-MATHBLOCK-02, T-MATHBLOCK-03, T-MATHBLOCK-04

Three sub-changes, ordered by risk (low → medium → low):

**5a. `@` infix at multiplicative level.**  
In `parse_multiplicative`, add an arm for `MathToken::At` → produce `MathExpr::MatMul(lhs, rhs)`. Precedence: parse lhs at `parse_unary`, then check for `@` before `*`/`/`. Add parser test: `parse("A @ B")` → `MatMul(Var("A"), Var("B"))`.

**5b. `A[i:j, k]` multi-axis slice grammar.** (MEDIUM RISK)  
Extend `parse_subscript` (called when a `[` follows a primary expression):
- After parsing the first index expression, peek for `MathToken::Colon`. If present, consume it, parse `stop` (optional), and produce a `SliceRange`.
- After each `SliceRange`, peek for `MathToken::Comma`. If present, parse the next axis.
- Produce `MathExpr::Slice { base, ranges }` when any axis contains a colon; keep `MathExpr::Subscript` for pure single-integer subscripts (no axis change to existing subscript eval).
- **Comma disambiguation:** commas inside a subscript `[...]` must not trigger function-call comma parsing. The math parser must enter a "subscript context" (boolean flag or parser sub-function) where commas separate axes rather than arguments.
- Verify: `parse("A[1:3, 0]")` → `Slice { base: Var("A"), ranges: [SliceRange{start:Int(1),stop:Int(3)}, SliceRange{start:Int(0),stop:Int(0)}] }`. (Single-integer axis treated as `start=i, stop=i+1` at eval time.)
- Verify: `parse("A[.., 2]")` → `Slice { base: Var("A"), ranges: [SliceRange{None,None}, SliceRange{Int(2),Int(2)+1}] }`.

**5c. `.method(args)` postfix normalisation.**  
Extend `parse_postfix` to recognise `.Ident(` following any primary expression. At parse time, normalise to `App("method", [receiver] ++ args)`. This avoids adding a `MethodCall` AST node in v1. Specifically handle `.T` (no parens) normalised to `App("transpose", [receiver])`.
- Verify: `parse("A.T")` → `App("transpose", [Var("A")])`.
- Verify: `parse("A.sum(0)")` → `App("sum", [Var("A"), Int(0)])`.
- Verify: `parse("A.mean(1)")` → `App("mean", [Var("A"), Int(1)])`.

**Risk:** Medium overall due to subscript comma disambiguation. The binder form `Sum(i, 1..n, ...)` uses `..` not `,` for its range, so the comma inside `[...]` is only ambiguous if the parser is in a shared expression context. Isolating subscript parsing with a context flag is the safest fix.

---

### T-MATHBLOCK-06 — Eval: `MatMul` arm → `Tensor::matmul`

**Scope:** `blocks/math/eval/mod.rs`  
**Estimate:** 0.5 day  
**Deps:** T-MATHBLOCK-03, T-BLAS-01 (mock matmul symbol for backend hook)

In `evaluate_expr`, add arm for `MathExpr::MatMul(lhs, rhs)`:
1. Evaluate `lhs` and `rhs` → both must be `MathValue::Tensor`.
2. Call `Tensor::matmul(&lhs_tensor, &rhs_tensor)` (already implemented in `tensor/matrix.rs`).
3. Check `BackendCapability::for_backend(CUDA).supports_matmul` and if available and tensor byte-size exceeds threshold, dispatch to `cuda_eval` path (runtime probe — no type-system involvement).

No change to `auto_select.rs` needed; extend `BackendCapability` to include `supports_matmul: bool`.

**Risk:** Low. `Tensor::matmul` already exists. The backend probe hook slot already exists in `auto_select.rs`.

---

### T-MATHBLOCK-07 — Eval: `Slice` arm → `tensor_slice`

**Scope:** `blocks/math/eval/mod.rs`, `blocks/math/tensor/indexing.rs`  
**Estimate:** 1 day  
**Deps:** T-MATHBLOCK-04, T-MATHBLOCK-05, T-NDARRAY-01 (NDArray view semantics)

In `tensor/indexing.rs`, add:
```
fn tensor_slice(tensor: &MathTensor, ranges: &[SliceRange]) -> MathTensor
```
Implementation: for each axis, extract `(start, stop)` with defaults (`start=0`, `stop=dim_size`). Compute a strided view or materialise a copy as a new `MathTensor`. Return the sliced tensor.

In `eval/mod.rs`, add arm for `MathExpr::Slice { base, ranges }`:
1. Evaluate `base` → `MathValue::Tensor`.
2. Call `tensor_slice`.
3. Return `MathValue::Tensor`.

Single-integer axis (`SliceRange { start: Int(i), stop: Int(i)+1 }`) reduces the axis dimension to 1 and then squeeze on that axis.

**Risk:** Medium. Strided view semantics inside the math block's internal `MathTensor` type must be validated against the existing `get`/`set` in `indexing.rs`. Do not attempt to connect this to `NDArray`'s `StorageBackend` view in v1 — keep `MathTensor` self-contained.

---

### T-MATHBLOCK-08 — Eval: `App("inv", [A])` arm with LAPACK FFI

**Scope:** `blocks/math/eval/mod.rs`, new `blocks/math/eval/tensor_functions.rs` additions  
**Estimate:** 2 days  
**Deps:** T-LAPACK-01 (`rt_lapack_dgetrf`, `rt_lapack_dgetri` in mock shim), T-NDARRAY-01

In `eval/mod.rs` `eval_function`, add arm `"inv"` (one argument):
1. Check arg is `MathValue::Tensor` with ndim=2 and square shape; else return `Err`.
2. Add `eval_inv(tensor: &MathTensor) -> Result<MathTensor, MathError>` to `tensor_functions.rs`.
3. `eval_inv` calls `rt_lapack_dgetrf` (LU factorisation in-place) then `rt_lapack_dgetri` (inversion using LU). These are extern symbols loaded from `libspl_cublas_mock.so` (interp mode) or `libspl_lapack.so` (native).
4. Handle `devInfo != 0` → `MathError::Singular`.

**FFI note:** The extern call path from inside the math block runtime is new. The pattern to follow is `eval/mod.rs` value bridge to `MathValue::Tensor` → extract raw pointer + shape → call `rt_lapack_*` extern → reconstruct `MathTensor` from result buffer. This is the highest implementation complexity item in v1.

**Risk:** HIGH. This is the first LAPACK FFI call originating inside the math block runtime, not from the main Simple interpreter. The extern resolution path (`spl_dlopen` → `libspl_cublas_mock.so`) must be confirmed to work from within the block evaluator context, not just from the interpreter's main eval loop. Verify interp-mode can load the symbol before writing the dispatch arm. If not, raise as a bug against the block eval FFI pathway.

---

### T-MATHBLOCK-09 — Eval: `App("solve", [A, b])` arm with LAPACK FFI

**Scope:** `blocks/math/eval/mod.rs`, `blocks/math/eval/tensor_functions.rs`  
**Estimate:** 1 day  
**Deps:** T-MATHBLOCK-08 (same FFI plumbing), T-LAPACK-01 (`rt_lapack_dgesv`)

Add `"solve"` arm (two arguments: matrix A, vector b):
1. Check A is 2D square, b is 1D with matching rows; else `Err`.
2. `eval_solve(a, b) -> Result<MathTensor, MathError>` calling `rt_lapack_dgesv`.
3. `devInfo != 0` → `MathError::Singular`.

Shares all FFI plumbing established in T-MATHBLOCK-08. If T-MATHBLOCK-08's FFI pathway works, this task is straightforward.

**Risk:** Medium (depends on T-MATHBLOCK-08 FFI pathway being green). Lower risk than `inv` because `dgesv` is a single call vs `dgetrf`+`dgetri`.

---

### T-MATHBLOCK-10 — Eval: axis-int extension for `sum` and `mean`

**Scope:** `blocks/math/eval/mod.rs`, `blocks/math/tensor/reduction.rs`  
**Estimate:** 0.5 day  
**Deps:** T-MATHBLOCK-05 (postfix normalisation for `.sum(axis)` → `App("sum", [A, axis])`)

Current `eval_sum_tensor` at `eval/mod.rs:410` dispatches `sum` only when called with one argument (the tensor). Extend:
- If called with two args `(tensor, axis_int)`: call `reduction::sum_axis(tensor, axis)` — a new function that reduces only along the specified axis, returning a tensor with that dimension removed.
- If called with one arg: existing full-reduce behaviour unchanged.
- Apply the same extension to `mean`.

In `tensor/reduction.rs`, add `sum_axis(t: &MathTensor, axis: usize) -> MathTensor` and `mean_axis`.

**Risk:** Low to Medium. Must be careful not to break the existing single-arg dispatch guard. The existing check `if args.len() == 1 && is_tensor(args[0])` must become `if args.len() >= 1 && is_tensor(args[0])`.

---

### T-MATHBLOCK-11 — Rendering: `MatMul`, `Slice`, and axis-reduction display

**Scope:** `blocks/math/rendering/`  
**Estimate:** 0.5 day  
**Deps:** T-MATHBLOCK-03, T-MATHBLOCK-04

- `MatMul(lhs, rhs)` → LaTeX: `lhs \cdot rhs`; Unicode text: `lhs @ rhs`.
- `Slice { base, ranges }` → LaTeX and text: `base[r0, r1, ...]` where each range renders as `start:stop` or `..` for open ranges.
- `App("sum", [A, Int(axis)])` → LaTeX: `\sum_{axis} A`; text: `A.sum(axis)`.
- `App("mean", [A, Int(axis)])` → LaTeX: `\overline{A}_{axis}`; text: `A.mean(axis)`.

**Risk:** Low.

---

### T-MATHBLOCK-12 — Spec: `math { A @ B + v }` and matmul scenarios

**Scope:** new `test/feature/usage/math_block_linalg_spec.spl`  
**Estimate:** 1 day  
**Deps:** T-MATHBLOCK-06, T-MATHBLOCK-11

Write interpreter-mode spec scenarios (all active, zero `skip()`):
- `evaluates A @ B` — 2×2 matrix times 2×2 matrix; check result shape and known values using mock backend deterministic output.
- `A @ B + c scalar broadcast` — matmul result plus scalar; validates operator precedence (`@` binds tighter than `+`).
- `evaluates (A @ B) @ C associativity` — left-association parenthesis check.
- `renders A @ B as unicode` — `.to_pretty()` contains `"@"`.
- `renders A @ B as LaTeX` — `.render_latex_raw()` contains `\cdot`.

Run with `SIMPLE_BLAS_BACKEND=mock`. All assertions use concrete values from mock shim deterministic output (zeros or identity — document expected values in spec comments).

**Risk:** Low once T-MATHBLOCK-06 and mock backend are working. Medium if the mock shim is not yet providing deterministic matmul results (coordinate with T-BLAS-01 owner).

---

### T-MATHBLOCK-13 — Spec: slice ops `A[i:j, ..]`

**Scope:** `test/feature/usage/math_block_linalg_spec.spl` (extend same file)  
**Estimate:** 1 day  
**Deps:** T-MATHBLOCK-07, T-MATHBLOCK-11

Add scenarios:
- `evaluates A[1:3]` on 1D tensor — result is sub-array of expected length.
- `evaluates A[0:2, 0:2]` on 2D 3×3 tensor — result is 2×2 sub-matrix.
- `evaluates A[.., 1]` column slice — result is 1D column vector.
- `renders A[1:3] as text` — `.to_pretty()` contains `"[1:3]"`.

All assertions use literal-constructed tensors in the math block (e.g., `math { A = [[1,2,3],[4,5,6],[7,8,9]]; A[0:2, 0:2] }`). No FFI required.

**Risk:** Low.

---

### T-MATHBLOCK-14 — Spec: `inv(A)` and `solve(A, b)` with mock backend

**Scope:** `test/feature/usage/math_block_linalg_spec.spl` (extend same file)  
**Estimate:** 1 day  
**Deps:** T-MATHBLOCK-08, T-MATHBLOCK-09, T-LAPACK-01

Add scenarios:
- `evaluates inv(I)` — identity matrix inverse is identity; mock shim returns identity for identity input. Verify result matches input shape.
- `evaluates solve(A, b) returns vector` — check result is 1D with correct length.
- `inv of singular matrix returns error` — pass a zero matrix; verify `MathError::Singular` or block evaluator error surface (depending on how math block exposes errors — document the current error surfacing mechanism).

**Note:** The mock shim must return deterministic non-trivial values for `inv` and `solve`. Coordinate with T-LAPACK-01 owner on what the mock shim returns for a 2×2 identity input.

**Risk:** Medium. Depends on the FFI pathway from T-MATHBLOCK-08 being confirmed working in interp mode. If T-MATHBLOCK-08's FFI validation reveals a blocker, these specs must be held until the blocker is resolved — do not skip them.

---

### T-MATHBLOCK-15 — Spec: axis reductions `A.sum(0)`, `A.mean(1)`

**Scope:** `test/feature/usage/math_block_linalg_spec.spl` (extend same file)  
**Estimate:** 0.5 day  
**Deps:** T-MATHBLOCK-10, T-MATHBLOCK-05

Add scenarios:
- `evaluates A.sum(0) reduces along axis 0` — 3×4 tensor; result shape is (4,).
- `evaluates A.mean(1) reduces along axis 1` — 3×4 tensor; result shape is (3,).
- `evaluates A.sum() full reduction` — existing behaviour unchanged; verify no regression.

All assertions check result shape and spot-check values using literal tensor construction inside the math block.

**Risk:** Low.

---

### T-MATHBLOCK-16 — PERF-SUGAR-002 observation + workaround documentation

**Scope:** `doc/08_tracking/feature_request/scilib_perf_sugar.md` update  
**Estimate:** 0.5 day  
**Deps:** T-MATHBLOCK-12 (must run the `A @ B + v` spec to measure actual alloc cost)

After T-MATHBLOCK-12 spec is green, profile the intermediate allocation cost for `math { A @ B + v }`. Document:
- Actual observed allocation count (should be 2 intermediates: one for `A @ B`, one for `result + v`).
- Time overhead vs explicit `linalg.gemm` call for a representative matrix size (e.g., 128×128).
- Workaround guidance: "do not use `math{}` in hot inner loops in v1; use explicit `linalg.gemm` calls instead."
- Promote PERF-SUGAR-002 from `anticipated` to `observed` in the tracking file.

**Risk:** Low (documentation task).

---

## v2 Sketch Tasks (out of scope for v1 impl — do not implement)

The following tasks are deferred to v2. They are listed here so v2 agents have a complete picture. No compiler files are modified for these items in v1.

### T-MATHBLOCK-V2-01 — HIR-lift: `math{}` as grammar-level node

**Scope:** Simple parser (`src/compiler_rust/compiler/src/hir/`)  
**Deps:** Compiler team commitment; PERF-SUGAR-002/003 both `fixed`

Add `math{}` as a first-class grammar node in the Simple parser, capturing the enclosed expression as an HIR sub-tree (not a string payload). This requires:
1. New grammar production in the Simple parser (the outer HIR-level parser, not the block-internal math parser).
2. HIR node type `MathExprHIR` holding a typed expression tree with scope-resolved variable references.
3. Type-environment pass over `MathExprHIR` nodes — if all tensor operands are statically typed `NDArray<Float64>`, the node is annotated as "BLAS-eligible".

This is a major compiler project. Do not begin until the runtime v1 extension is stable and the compiler team has committed scope.

**Cross-area deps:** Requires a complete HIR understanding of the surrounding type environment — the entire type inference pass must be complete and stable before HIR-lift begins.

---

### T-MATHBLOCK-V2-02 — Compile-time type-directed dispatch to cuBLAS

**Scope:** HIR codegen (`src/compiler_rust/compiler/src/codegen/`)  
**Deps:** T-MATHBLOCK-V2-01

At codegen for a "BLAS-eligible" `MathExprHIR` node: emit direct `rt_blas_dgemm` / `rt_lapack_dgesv` calls rather than dispatching through the runtime evaluator. The runtime evaluator becomes the fallback path for dynamically-typed or unsupported math expressions.

Requires `TypeAnnotatedMathExpr` IR: existing `MathExpr` AST is demoted to fallback; the annotated form is the primary codegen input.

---

### T-MATHBLOCK-V2-03 — FMA kernel fusion in math block

**Scope:** `blocks/math/eval/` + HIR codegen  
**Deps:** T-MATHBLOCK-V2-02, PERF-SUGAR-008 (`fixed`)

Fuse adjacent `MatMul` + `Add` into a single `gemm` call with non-zero `beta` (i.e., `C = alpha*A*B + beta*C`). This eliminates the two intermediate allocations in `A @ B + c`. In the runtime path (v1 fallback), this is a peephole optimisation over the `MathExpr` AST; in the HIR path (v2 primary), it is a codegen lowering rule.

---

### T-MATHBLOCK-V2-04 — `linalg{}` / `array{}` keyword aliases

**Scope:** `src/compiler_rust/compiler/src/blocks/mod.rs`  
**Deps:** T-MATHBLOCK-V2-01 (or may land in v1 if just alias arms)

If user ergonomics warrant scoping intent, add `linalg {}` and `array {}` as zero-cost aliases that dispatch to `MathBlock.evaluate(payload)`. This is a one-line match arm addition per keyword and carries no compiler capability — it is purely a user-visible naming choice. Decision deferred to v2 UX review.

---

### T-MATHBLOCK-V2-05 — Type-directed NDArray<Float32> dispatch (sgemm)

**Scope:** HIR codegen, `blocks/math/eval/`  
**Deps:** T-MATHBLOCK-V2-02

Extend BLAS-eligible dispatch to `NDArray<Float32>` → `rt_blas_sgemm`. Currently the runtime probe only checks for `f64` tensors. v2 type-directed dispatch makes this a static decision at codegen.

---

## Task Summary Table

| ID | Title | Days | v1/v2 | Deps |
|---|---|---|---|---|
| T-MATHBLOCK-01 | Lexer: `@` token | 0.5 | v1 | — |
| T-MATHBLOCK-02 | Lexer: `:` slice token | 0.5 | v1 | — |
| T-MATHBLOCK-03 | AST: `MatMul` variant | 0.5 | v1 | T-MATHBLOCK-01 |
| T-MATHBLOCK-04 | AST: `Slice` node + `SliceRange` | 0.5 | v1 | T-MATHBLOCK-02 |
| T-MATHBLOCK-05 | Parser: `@` infix, `[i:j,k]` subscript, `.method` normalisation | 2 | v1 | T-MATHBLOCK-01/02/03/04 |
| T-MATHBLOCK-06 | Eval: `MatMul` arm → `Tensor::matmul` | 0.5 | v1 | T-MATHBLOCK-03, T-BLAS-01 |
| T-MATHBLOCK-07 | Eval: `Slice` arm → `tensor_slice` | 1 | v1 | T-MATHBLOCK-04/05, T-NDARRAY-01 |
| T-MATHBLOCK-08 | Eval: `App("inv")` arm + LAPACK FFI | 2 | v1 | T-MATHBLOCK-05, T-LAPACK-01 |
| T-MATHBLOCK-09 | Eval: `App("solve")` arm + LAPACK FFI | 1 | v1 | T-MATHBLOCK-08, T-LAPACK-01 |
| T-MATHBLOCK-10 | Eval: axis-int extension for `sum`/`mean` | 0.5 | v1 | T-MATHBLOCK-05 |
| T-MATHBLOCK-11 | Rendering: MatMul, Slice, axis-reduction display | 0.5 | v1 | T-MATHBLOCK-03/04 |
| T-MATHBLOCK-12 | Spec: `A @ B + v` matmul scenarios | 1 | v1 | T-MATHBLOCK-06/11 |
| T-MATHBLOCK-13 | Spec: slice ops `A[i:j, ..]` | 1 | v1 | T-MATHBLOCK-07/11 |
| T-MATHBLOCK-14 | Spec: `inv(A)` and `solve(A, b)` mock backend | 1 | v1 | T-MATHBLOCK-08/09, T-LAPACK-01 |
| T-MATHBLOCK-15 | Spec: axis reductions `A.sum(0)`, `A.mean(1)` | 0.5 | v1 | T-MATHBLOCK-10/05 |
| T-MATHBLOCK-16 | PERF-SUGAR-002 observation + workaround doc | 0.5 | v1 | T-MATHBLOCK-12 |
| T-MATHBLOCK-V2-01 | HIR-lift: `math{}` as grammar-level node | sketch | v2 | compiler team commitment |
| T-MATHBLOCK-V2-02 | Compile-time type-directed dispatch to cuBLAS | sketch | v2 | T-MATHBLOCK-V2-01 |
| T-MATHBLOCK-V2-03 | FMA kernel fusion in math block | sketch | v2 | T-MATHBLOCK-V2-02, PERF-SUGAR-008 |
| T-MATHBLOCK-V2-04 | `linalg{}`/`array{}` keyword aliases | sketch | v2 | T-MATHBLOCK-V2-01 or standalone |
| T-MATHBLOCK-V2-05 | Type-directed NDArray<Float32> sgemm dispatch | sketch | v2 | T-MATHBLOCK-V2-02 |

**v1 total:** 16 tasks, ~12.5 person-days  
**v2 total:** 5 sketch tasks (no day estimate — design-level only)

---

## Sequencing (v1 implementation order)

```
T-MATHBLOCK-01  ──┐
T-MATHBLOCK-02  ──┤
                  ▼
T-MATHBLOCK-03 ◄─ 01
T-MATHBLOCK-04 ◄─ 02
                  │
T-MATHBLOCK-05 ◄─ 01/02/03/04  (2 days — critical path)
                  │
        ┌─────────┼─────────────┬──────────────┐
        ▼         ▼             ▼              ▼
T-MATHBLOCK-06  T-MATHBLOCK-07  T-MATHBLOCK-08  T-MATHBLOCK-10
(+T-BLAS-01)   (+T-NDARRAY-01) (+T-LAPACK-01)
                                │
                         T-MATHBLOCK-09
                         (+T-LAPACK-01)
        │         │             │              │
        └─────────┴─────────────┴──────────────┘
                  │
T-MATHBLOCK-11 ◄─ 03/04 (can run in parallel with 06–10)
                  │
        ┌─────────┼─────────────┬──────────────┐
        ▼         ▼             ▼              ▼
T-MATHBLOCK-12  T-MATHBLOCK-13  T-MATHBLOCK-14  T-MATHBLOCK-15
(+11,06)        (+11,07)        (+08/09)        (+10/05)
                  │
T-MATHBLOCK-16 ◄─ T-MATHBLOCK-12
```

**Critical path:** T-01/02 → T-05 (parser, 2 days) → T-08 (inv FFI, 2 days) → T-14 (spec, 1 day) = 5 days minimum elapsed, gate on T-LAPACK-01 sibling.

---

## Acceptance Criteria (v1 complete)

- [ ] `bin/simple test test/feature/usage/math_block_linalg_spec.spl` passes in interpreter mode with `SIMPLE_BLAS_BACKEND=mock`; zero `skip()`, zero TODO→NOTE.
- [ ] `parse("A @ B + c")` produces `Add(MatMul(Var("A"), Var("B")), Var("c"))` — `@` binds tighter than `+`.
- [ ] `parse("A[1:3, 0]")` produces `Slice { ranges: [SliceRange{1,3}, SliceRange{0,1}] }` (unit test).
- [ ] `parse("A.T")` produces `App("transpose", [Var("A")])` (unit test).
- [ ] `inv` and `solve` eval arms green against mock shim deterministic output.
- [ ] `A.sum(0)` and `A.mean(1)` reduce along the specified axis; existing full-reduce unaffected.
- [ ] Rendering: `MatMul` → `@` in text, `\cdot` in LaTeX; `Slice` → `A[i:j,k]`; axis-reduction → correct text/LaTeX.
- [ ] PERF-SUGAR-002 promoted from `anticipated` to `observed` in `scilib_perf_sugar.md`; workaround guidance recorded.
- [ ] Zero df ops (`df['col']`, `groupby`) introduced into `math{}` at any point.
- [ ] Zero primitive type leaks at any public-facing surface touched by this area.
- [ ] No `--mode=native` or `--mode=smf` bypass in any spec.

---

## Risk Register

| Risk | Severity | Mitigation |
|---|---|---|
| `@` operator precedence — wrong binding vs `*` or `^` | Medium | Explicit unit test in parser before eval work starts; if wrong, fix is one-line precedence level change |
| `:` token inside `[...]` comma ambiguity | Medium | Subscript-context flag in parser; do not enter function-call comma logic inside `[...]` |
| LAPACK FFI from inside math block eval path (new) | High | Validate the extern symbol resolution path from block evaluator context before T-MATHBLOCK-08 implementation; file bug immediately if it fails; do not work around with `--mode=native` |
| Mock shim does not provide deterministic `inv`/`solve` output | Medium | Coordinate with T-LAPACK-01 owner; define expected mock return values before writing T-MATHBLOCK-14 specs |
| Axis-int arg breaks existing single-arg `sum` dispatch | Low | Guard with `args.len()` check; add regression scenario for full-reduce in T-MATHBLOCK-15 |
| PERF-SUGAR-001 not landed when math-block work starts | High (inherited) | math-block eval creates intermediate tensors; without fast alloc, specs time out; do not start T-MATHBLOCK-06/07/08 until PERF-SUGAR-001 is `fixed` |
