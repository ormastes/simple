# `type_system/expr_infer.spl` matches a STRUCT against enum-variant patterns — every arm is dead

- Status: CLOSED (not reproducible)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
  were removed; the live inference engine is `HmInferContext` in
  `src/compiler/30.types/type_infer/`. Record + recovery shas:
  `doc/09_report/compiler/type_system_dead_inference_cluster_removal_2026-08-01.md`
- **Status (original):** OPEN
- **Date:** 2026-08-01
- **Severity:** HIGH (whole-module wrong-code) / **not currently shipping** — module is unwired
- **Component:** compiler / `30.types/type_system` (AST-level Hindley-Milner port)
- **Parent defect:** `doc/08_tracking/bug/case_bare_ident_is_irrefutable_binding_2026-08-01.md`
- **Confirmed by:** execution, with a passing control and a failing sentinel (below)

## Why this supersedes the "22 flagged arms" entry

The parent sweep flagged 22 arms in `expr_infer.spl` on a name-existence test.
Investigating them found the real defect is one level up and an order of
magnitude larger: **it is not 22 bad arms in otherwise-working code — the entire
`infer_expr` dispatch is inert.** Fixing the 22 arms individually would change
nothing, because no arm in the function can ever be selected.

Three independent, compounding faults, each sufficient on its own:

### 1. The scrutinee is a struct, the patterns are enum-variant patterns

`src/compiler/10.frontend/parser_types_expr.spl`:

```
struct Expr:          # <- line 204
    kind: ExprKind
    span: Span

enum ExprKind:        # <- line 210
    IntLit(i64)
    ...
```

`infer_expr` does `match expr:` where `expr: Expr` — the **struct** — and then
writes 63 top-level `case IntLit(...)`-style arms. It must be `match expr.kind:`.
This is the struct-wrapping-an-enum compound error, in its purest form.

### 2. A bare `case Nil:` at line 80 swallows the remainder

`Nil` is not an `ExprKind` variant (the variant is `NilLit`). Per the parent
defect it parses as an irrefutable binding, so arms 83–541 — `Symbol`,
`FString`, `Identifier`, `Binary`, `Call`, `MethodCall`, every arm below it, and
the final `case _:` — are unreachable.

### 3. 44 of 63 arm names are not `ExprKind` variants at all

Only **18** of the 63 top-level arm names exist in `ExprKind` (52 variants).
The other 44 are Rust-seed AST spellings with no Simple counterpart:

```
Array BlockExpr Bool CastElse CastOr CastOrReturn Coalesce ContractOld
ContractResult Dict DictSpread DoBlock Exists FieldAccess Float Forall FString
FunctionalUpdate Go GridLiteral Identifier IfExpr Integer MacroInvocation New
Nil OptionalMethodCall Path Slice Spread String StructInit Symbol TensorLiteral
Tuple TupleIndex TypedFloat TypedInteger TypedString UnwrapElse UnwrapOr
UnwrapOrReturn VecLiteral
```

Correct spellings differ systematically: `Integer`→`IntLit`, `String`→`StringLit`,
`Bool`→`BoolLit`, `Nil`→`NilLit`, `Array`→`ArrayLit`, `Tuple`→`TupleLit`,
`Dict`→`DictLit`, `Identifier`→`Ident`, `FieldAccess`→`Field`, `IfExpr`→`If`,
`StructInit`→`StructLit`. `Symbol`, `FString`, `TypedInteger`, `TypedFloat`,
`TypedString`, `Path`, `Slice`, `TupleIndex`, `Go`, `New`, `VecLiteral`,
`MacroInvocation`, `Spread`, `DictSpread`, `FunctionalUpdate`, `ContractResult`,
`ContractOld`, `Forall`, `Exists`, `DoBlock`, `GridLiteral`, `TensorLiteral`,
`BlockExpr`, `I18n*`, `UnwrapOr/Else/OrReturn`, `Cast{Or,Else,OrReturn}`,
`Coalesce`, `OptionalMethodCall` have **no `ExprKind` variant at all** — they are
not renames, they are absent concepts.

### 4. Every helper the arm bodies call is undefined repo-wide

`/usr/bin/grep -rn "fn <name>" --include='*.spl' src/` returns **0** for all of:

```
engine_fresh_var  type_Int  type_Float  type_Str  type_Nil  type_Bool
env_contains  elems_len  start_value  end_value  step_value
condition_value  value_value
```

`has_start` / `has_end` / `has_step` / `has_condition` / `has_value` / `has_args`
exist only as *struct fields on other types*, never as bindings in these scopes.
So even a correctly-dispatched arm body could not execute. The file nevertheless
**compiles with warnings only** — no error is reported for any of this, which is
the `lint`/`check` fail-open hole recorded in memory.

## Execution evidence

Probe: `struct EX { kind: EKind, span: i64 }`, reproducing the exact
`match <struct>:` + ctor-arms + bare-`Nil` shape. Run on
`src/compiler_rust/target/bootstrap/simple`.

```
--- CONTROL (match on .kind) ---
PASS  1 -> INT
PASS  2 -> BOOL
PASS  3 -> NIL
PASS  4 -> IDENT
PASS  5 -> WILD
--- PROBE (expr_infer.spl shape; expectations assume arms work) ---
FAIL  1 -> BARE-NIL-SWALLOWED  (expected INT)
FAIL  2 -> BARE-NIL-SWALLOWED  (expected BOOL)
FAIL  4 -> BARE-NIL-SWALLOWED  (expected IDENT)
FAIL  5 -> BARE-NIL-SWALLOWED  (expected WILD)
--- SENTINEL (deliberately wrong; MUST FAIL) ---
FAIL  1 -> INT  (expected THIS-EXPECTATION-IS-WRONG)
```

Control passes on all five, sentinel fails ⇒ the harness is live and falsifiable.
The decisive row is `PROBE 1`: `IntLit` is matched by an arm **above** the bare
`Nil` arm and is *still* swallowed. That proves fault #1 independently of fault
#2 — constructor-pattern arms do not match a struct scrutinee either. Rewriting
the arm names alone would therefore not have fixed anything.

## Blast radius — assessed, and the reason nothing was rewritten

**Currently zero shipped impact.** `infer_expr` is AST-level and is reachable
only through `type_system/{checker,module_check,bidirectional}.spl`. The
driver's sole type-inference pass, `run_typecheck_warn_pass`
(`80.driver/driver_hir_pipeline_passes.spl:68`), uses `HmInferContext` from
`30.types/type_infer/` — a **different**, HIR-level engine — and is itself gated
behind `SIMPLE_TYPECHECK_WARN=1` and warn-only
(`80.driver/driver_hir_pipeline_lowering.spl:365`). No caller of the
`type_system` `TypeChecker` exists in `80.driver/` or `src/app/`. Combined with
fault #4, this module has **never executed**.

**Which is exactly why the fix was not attempted here.** A correct repair is a
full rewrite of ~500 lines of type inference: re-dispatch on `.kind`, drop or
re-map 44 arm names against the real 52-variant `ExprKind`, and *newly author*
the 13 missing helper functions that no current code defines. There is no
"correct" prior behaviour to restore and no test that exercises it — the port
has been inert since it was written, so nothing downstream has adapted to a
wrong inference result (it never produced one). A speculative rewrite would be
introducing a new, unverified type-inference engine under the guise of a bug
fix. Per the standing rule, the safe subset is landed as this record.

## What a real fix must do

1. `match expr.kind:` — dispatch on the enum, never the wrapper struct.
2. Use the 52 real `ExprKind` spellings; delete arms for concepts `ExprKind`
   does not model rather than inventing variants.
3. Define the 13 missing helpers, or import the `type_infer/` equivalents.
4. **Unsupported kinds must fail loudly.** The present fallback returns
   `Ok(engine_fresh_var(engine))` — a plausible default that would silently
   green-light any unhandled expression. It must return an explicit
   `Err(TypeError.Other("infer_expr: unhandled ExprKind ..."))`.
5. Land behind the existing `SIMPLE_TYPECHECK_WARN` gate and measure the
   diagnostic count before considering it non-warn.

Alternative worth costing first: **delete `type_system/expr_infer*.spl`** and
consolidate on the live HIR-level `30.types/type_infer/` engine. Two parallel
inference implementations, one of them inert and undefined-at-the-leaves, is the
larger defect.

## Siblings with the same shape (not yet audited)

- `30.types/type_system/bidirectional.spl` — also does `match expr:` on the
  struct; line 133 `case IfExpr(...)` is in the parent sweep's confirmed table.
- `30.types/type_system/expr_infer_ops.spl:222` `case ChannelRecv:` — bare
  identifier, confirmed by the parent sweep.
- `30.types/type_system/module_check.spl` — 48 case-arms, unaudited.
