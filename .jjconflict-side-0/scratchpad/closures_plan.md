# Native Closures / Lambdas — Implementation Plan (#165)

Scope: `HirExprKind::Lambda` and first-class function values on the native
`--entry` build path (`bin/simple native-build`, which interprets
`src/compiler/*.spl`). Unblocks #155 (array `map`/`filter`/`fold`).

## 1. Ground-truth status (measured on origin/main, worktree)

Lambda syntax is `\x: expr` / `\a, b: expr` (see
`doc/07_guide/quick_reference/syntax_quick_reference.md:680`).

| Repro | Native `--entry` | Interp oracle | Notes |
|-------|------------------|---------------|-------|
| `val f = \x: x+1; f(5)` | **6** ✓ | 6 | direct call — already works |
| `val n=10; val f = \x: x+n; f(5)` | **15** ✓ | 15 | capture-by-read — already works |
| `val add = \a,b: a+b; add(3,4)` | **7** ✓ | 7 | multi-arg direct call — works |
| `apply(\x: x+1, 5)` (HOF) | **build FAIL** | 6 (correct) | lambda passed as value |
| `apply(\x: x*2, 5)` (HOF) | **build FAIL** | 10 (correct) | anon lambda as value |
| `apply(inc, 5)` (named fn as value) | **build FAIL** | **129256973668817 (garbage)** | interp oracle broken here |

**What already works:** any *directly-called* val-bound lambda, including
capture-by-read of outer locals, via inline beta-reduction (lambda-lift at the
call site). Implemented in `try_inline_lambda_call`
(`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:1053`),
populated by `lambda_bindings[...] = let_init` in
`src/compiler/50.mir/mir_lowering_stmts.spl:134-141`; the binding map is declared
in `src/compiler/50.mir/mir_lowering_types.spl:113`.

**The actual gap = first-class function values** (lambda or named fn *passed to*
a HOF, stored in a field, returned, or invoked indirectly). This is what #155's
`map`/`filter`/`fold` require.

**Oracle status (corrected):** the interpreter oracle is **reliable for
lambda-as-value** (returns correct 6 / 10 for `apply(\x:…, …)`) and is the
verification oracle to use for the full feature. It is **broken only for a
*named* function passed as a value** (`apply(inc, 5)` → garbage boxed-pointer
artifact). For that sub-case, verify by construction / fix the interpreter's
function-value boxing separately; do not chase the garbage value.

## 2. Root-cause gap chain (parser → HIR → MIR → backend)

The blocker surfaces *before* the lambda: the **function-pointer parameter type
`(i64) -> i64` does not parse as a type**. Isolation proof:
`fn apply(g: (i64) -> i64, v: i64) -> i64: return v` fails at phase-3 HIR
lowering with `unresolved name: i64` (×2) and `unresolved name: v` even though
the body never calls `g`. Removing the fn-type param (`g: i64`) builds fine.

Because the param type fails to parse, the whole param list is not registered as
symbols, so `g`, `v`, and the two `i64`s decay to *expression* idents and hit the
`unresolved name` error at
`src/compiler/20.hir/hir_lowering/expressions.spl:191`.

Layer-by-layer:

1. **Parser (ROOT).** `parser_parse_type()`
   (`src/compiler/10.frontend/core/parser.spl:379`) begins by requiring an
   *identifier* token (`kind == 6`) or `dyn`. It has **no branch for a `(`-led
   function type** `(T, …) -> U`. When the type starts with `(`, it falls
   through and the surrounding param parser mis-consumes the `(i64) -> i64`
   tokens.
   - **Encoding sub-gap:** `parser_parse_type()` returns an *integer type-id*
     (`TYPE_VOID=0`, `TYPE_ANY=12`, `TYPE_NAMED_BASE=1000`; see
     `src/compiler/10.frontend/core/types.spl:212-256`). There is **no
     `TYPE_FUNCTION` id**, and a bare integer cannot carry the param/return
     signature. The fix therefore needs a new encoding: a `TYPE_FUNCTION` base id
     plus a **side-table** (indexed like `TYPE_NAMED_BASE`) recording the param
     type-ids and return type-id for each parsed function type.

2. **Flat→AST bridge.** `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`
   (type-id → `TypeKind` mapping, near line 197 `if type_expr_idx == TYPE_VOID`)
   must map the new `TYPE_FUNCTION` id (reading the side-table) into
   `TypeKind.Function(param_types, ret)`.

3. **HIR type lowering — ALREADY DONE.**
   `src/compiler/20.hir/hir_lowering/types.spl:244-249` already lowers
   `TypeKind.Function(params, ret)` → `HirTypeKind.Function(...)`. No work here
   once (1)+(2) feed it.

4. **HIR expr lowering — mostly done.** `ExprKind.Lambda` →
   `HirExprKind.Lambda(hir_params, hir_body, [])`
   (`src/compiler/20.hir/hir_lowering/expressions.spl:467-482`). Captures list is
   hard-coded empty `[]`; capture analysis exists separately in
   `src/compiler/35.semantics/lint/closure_capture.spl` and must be wired in for
   capturing closures (Phase C only).

5. **MIR lowering (the real work).** Two things are missing:
   - **Lambda as a value operand.** Today a `Lambda` HIR node only has meaning at
     a direct call site (beta-reduction). To pass it to a HOF, the lambda must be
     *lifted to a synthesized top-level MIR function* and materialized as a
     **function-pointer operand** (`MirOperand` of a global function symbol).
   - **Indirect call.** `apply`'s body `g(v)` — where `g` is a *local of
     function type*, not a `Var` resolving to a known symbol — must lower to an
     **indirect call through the fnptr local**. `lower_call`
     (`switch_operators_calls.spl:1082`) currently only builds *direct* calls
     (it early-returns to `is_direct=false` when the callee is in `local_map`,
     then has no indirect-call emit path).
   - ⚠️ **Ownership:** both live in
     `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`, which is
     **owned by another lane / off-limits for this task.**

6. **Backend.** `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`
   must emit the fnptr constant and an LLVM indirect `call` through a value.
   ⚠️ **Also off-limits for this task.**

## 3. Representation decision

- **Non-capturing lambda** (and named fn as value): lower to a **top-level
  (lifted) function + function pointer**. The value is just the function
  address; the indirect call passes args directly. No heap. This covers #155's
  common `map`/`filter`/`fold` usage where the lambda closes over nothing (or
  only over immutable module-level state).
- **Capturing lambda**: needs a **heap environment** — a synthesized struct
  holding the captured locals, allocated at the point the lambda becomes a
  value; the lifted function takes the env pointer as a hidden first parameter
  (a `{fnptr, env*}` closure pair, or a thunk). Capture set comes from
  `closure_capture.spl`. This is strictly larger and should be a later phase.
  Note: *direct-call* capture already works today by beta-reduction (outer
  locals stay in `local_map`); the heap env is only needed once the lambda
  escapes as a value.

## 4. Phased implementation order

- **Phase A — Parser fn-type (MINIMAL-VIABLE first step, allowed files).**
  Add the `(`-led function-type grammar to `parser_parse_type()` +
  `TYPE_FUNCTION` id + signature side-table (parser.spl / types.spl), and map it
  in `convert_nodes.spl`. Result: HOFs with fnptr params *parse and type-lower*
  (HIR `HirTypeKind.Function` already handled). **On its own this does NOT make
  `apply(...)` run** — MIR/backend indirect-call is still missing — so the build
  must **stay a loud fail** at MIR, never build-and-return-garbage. Because it
  can't produce a correct end-to-end result alone, it is *not* a landable slice
  under this task's gate (see §5); it is the first commit of the full feature.

- **Phase B — Non-capturing first-class values (MVP of the actual feature).**
  Lambda-lift non-capturing `Lambda` nodes to top-level MIR functions; emit a
  fnptr operand when a lambda/named-fn is used as a value; add the indirect-call
  path in `lower_call`; add fnptr emit + indirect `call` in the backend. Verify
  against the (reliable) lambda-as-value oracle: `apply(\x: x+1, 5)` → 6,
  `apply(\x: x*2, 5)` → 10. Fix the interpreter's named-fn-as-value boxing so
  `apply(inc, 5)` also yields a real value (or verify by construction).
  ⚠️ Requires switch_operators_calls.spl + core_codegen.spl → **needs the owning
  lane, or explicit re-assignment of ownership.**

- **Phase C — Capturing closures (heap env).** Wire `closure_capture.spl`
  capture sets into HIR `Lambda.captures`; synthesize env struct; pass env
  pointer to the lifted function; allocate at escape sites. Enables closures that
  outlive their defining scope.

- **Phase D — #155 array HOFs.** Implement `map`/`filter`/`fold` lowering to
  invoke the fnptr per element (touches `method_calls_literals.spl` — another
  owned file). Depends on Phase B.

**Minimal-viable milestone = Phase B** (the first phase that makes a real new
program — lambda passed to a HOF — build and run correctly). Phase A is a
prerequisite sub-step, not independently shippable.

## 5. Slice decision for THIS task: PLAN ONLY (no code landed)

No minimal slice is safely landable under the gate, for two independent reasons:

1. **File ownership.** Completing even the smallest end-to-end case
   (`apply(\x:…, v)`) requires the indirect-call operand + emit in
   `switch_operators_calls.spl` and fnptr codegen in `core_codegen.spl` — both
   explicitly **off-limits** for this task. The existing lambda lowering
   (`try_inline_lambda_call`) also already lives in the forbidden
   `switch_operators_calls.spl`, so there is no lambda-lowering file this task is
   permitted to edit meaningfully.
2. **Multi-layer feature.** A parser-only change (Phase A, allowed) makes nothing
   run correctly by itself; per HARD RULE 2 it must remain a loud build-fail, so
   it is not a "builds-and-returns-correct" slice.

Everything that *could* be a slice (direct-call / capture-by-read / multi-arg
lambda) **already works** on origin/main — there is nothing to add there.

Therefore: deliver the plan; land no code. (Corrected from an earlier draft: the
blocker is ownership + feature scope, **not** a broken oracle — the oracle is
correct for lambda-as-value.)
