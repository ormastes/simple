# `type_system` siblings: struct-scrutinee audit (`bidirectional`, `module_check`, `expr_infer_ops`)

- **Status:** OPEN (file-only; no repair attempted — see Decision)
- **Date:** 2026-08-01
- **Severity:** HIGH (wrong-code shape) / **not currently shipping — all three are unwired**
- **Component:** compiler / `30.types/type_system`
- **Sibling of:** `doc/08_tracking/bug/expr_infer_matches_struct_against_enum_variants_2026-08-01.md` (landed `158bc0c57270`)
- **Parent defect:** `doc/08_tracking/bug/case_bare_ident_is_irrefutable_binding_2026-08-01.md`
- **Confirmed by:** execution, with a passing control and a deliberately-failing sentinel

## Verdicts

| File | Struct-scrutinee defect? | Wired? |
|---|---|---|
| `bidirectional.spl:72` (`check_expr`) | **YES** — `match expr:` on `struct Expr` | **NO** |
| `module_check.spl:515` / `:569` (`ast_type_to_inference_type[_engine]`) | **YES** — `match ast_ty:` on `struct Type` | **NO** |
| `expr_infer_ops.spl:222` | **NO — does not reproduce** | **NO** |

## The "5 driver/app callers" premise for `bidirectional.spl` is FALSE

The audit brief flagged `bidirectional.spl` as WIRED with 5 callers in
`src/compiler/80.driver/**` or `src/app/**`. It is not. Those hits are
**name collisions**, not imports: `check_expr` and `synthesize_expr` are generic
names independently defined in `bidir_phase1a/b/c/d.spl`,
`bidirectional_inferencer.spl`, `type_infer/inference_expr.spl`, and
`desugar/suspension_analysis.spl`. None of them import
`compiler.types.type_system.bidirectional`.

The complete set of imports crossing into the `30.types/type_system/` package
from anywhere else in `src/` or `test/` is **two lines**:

```
src/compiler/80.driver/driver_hir_pipeline_lowering.spl:31: use compiler.types.type_system.effect_pass.{run_effect_pass}
src/compiler/90.tools/query_helpers.spl:8:                   import compiler.types.type_system.checker.{TypeError}
```

`effect_pass.spl` imports only `compiler.hir.hir`, `hir_definitions`,
`common.effects`, and `common.effects_solver` — **nothing from the inference
cluster**. `query_helpers.spl` takes the `TypeError` type alone.

So `checker.spl` → `bidirectional.spl` → `expr_infer.spl` → `module_check.spl` →
`expr_infer_ops.spl` is a **closed, self-referential island with zero external
entry points**. Same disposition as `expr_infer`: file precisely, do not repair.

## 1. `bidirectional.spl` — `check_expr` (line 72)

`fn check_expr(engine, expr: Expr, expected: Type, env)` does `match expr:` —
the **struct** (`parser_types_expr.spl:204`, `struct Expr { kind: ExprKind, span }`).
It must be `match expr.kind:`. All 9 named top-level arms are therefore dead.

Arms present, checked against the 52 `ExprKind` variants:

| Arm | In `ExprKind`? | Note |
|---|---|---|
| `Integer(n)` | NO | variant is `IntLit` |
| `Float(f)` | NO | variant is `FloatLit` |
| `Lambda(...)` | yes | |
| `IfExpr(...)` | NO | variant is `If` |
| `MatchCase(...)` | yes | |
| `Array(elements)` | NO | variant is `ArrayLit` |
| `Tuple(elements)` | NO | variant is `TupleLit` |
| `Dict(pairs)` | NO | variant is `DictLit` |
| `Call(callee, args)` | yes | |

Note the difference from `expr_infer`: `check_expr` has **no bare-ident
irrefutable arm**, so its trailing `case _:` (line 287) *is* reachable. That is
worse in one specific way — instead of failing, every expression silently
degenerates to the default path:

```
case _:
    val inferred = synthesize_expr(engine, expr, env)?
    engine_unify(engine, inferred, expected)?
    Ok(expected)
```

This is exactly the "silent fallback" shape that must become an explicit `Err`.
It is doubly inert because `synthesize_expr` is an alias for
`type_system.expr_infer.infer_expr` — the function already proven dead in the
sibling report.

Additional defects in the same file:

- `infer_with_expected` (line 514, the only symbol `checker.spl` imports) calls
  three identifiers that **do not exist repo-wide**: `has_expected`,
  `expected_value`, `infermode_Check`. (`has_expected` exists only as an unrelated
  method on `70.backend/backend/vhdl/vhdl_clock_ports.spl:119`.)
- Lines 467, 479, 490, 500 call `ast_type_to_inference_type_engine(engine, ...)`
  with **reversed arguments** — the signature is `(ast_ty: AstType, engine: InferenceEngine)`.
- Undefined helpers used by arm bodies: `type_Int`, `type_Float`, `engine_unify`,
  `engine_fresh_var` — `0` definitions each for `^\s*(fn|me) <name>` across `src/`.

## 2. `module_check.spl`

Split verdict — **the 48-arm count conflates two different situations.**

**Fine:** `match item:` at lines 152 and 389 scrutinises `item: Node`, and
`compiler/10.frontend/ast.spl:53` declares `enum Node:`. Correct enum-on-enum
form. (Four arm names — `Impl`, `TypeAlias`, `Const`, `Static` — are still not
`Node` variants; `Node` has only `Function Struct Class Enum Trait Other`. Those
four arms are dead, but they fall through to the arm's own `case _:` rather than
poisoning the dispatch.)

**Broken:** `ast_type_to_inference_type` (line 515) and
`ast_type_to_inference_type_engine` (line 569) both do `match ast_ty:` where
`AstType` is `compiler.frontend.parser_types_expr.Type` — and
`parser_types_expr.spl:23` declares `struct Type { kind: TypeKind, span }`.
Same struct-scrutinee defect. Must be `match ast_ty.kind:`.

Arms vs the 12 `TypeKind` variants
(`Named Tuple Array Function Optional Reference Atomic Isolated Union Projection Infer Error`):

- `Simple(name)` — **not a variant** (`Named(text, [Type])` covers it)
- `Generic(name, args)` — **not a variant** (also `Named`)
- `Optional`, `Array`, `Tuple`, `Function` — exist, but unreachable anyway.

Silent fallback, again requiring an explicit `Err`:

```
case _:
    # Unsupported type - return fresh variable
    checker_fresh_var(checker)
```

Every helper both functions call is **undefined repo-wide** (`0` files each):
`checker_fresh_var`, `type_Named`, `type_Generic`, `type_Optional`, `type_Array`,
`type_Tuple`, `type_Function`, `type_Bool`, `type_Str`, `type_Unit`, `args_map`,
`elems_map`, `params_map`, `has_ret`, `ret_value`.

`ast_type_to_inference_type_engine` has 5 in-package callers
(`_StmtCheck/bindings_check.spl`, `expr_infer.spl`, `expr_infer_calls.spl`,
`type_utils.spl`, `bidirectional.spl`) — all inside the same unwired island.

## 3. `expr_infer_ops.spl:222` — reported shape DOES NOT REPRODUCE

Every scrutinee in this file is a genuine enum:

- `infer_binary` line 24: `match op:` — `op: BinOp`, and
  `parser_types_expr.spl:505` declares `enum BinOp:`. Correct.
- `infer_unary` line 184: `match op:` — `op: UnaryOp`,
  `parser_types_expr.spl:557` declares `enum UnaryOp:`. Correct.
- Lines 158, 213, 224: `match engine_resolve(engine, ...):` — an inference
  `Type` from `20.hir/inference/types.spl:31`, `enum Type:`. Correct.

**No struct-vs-enum defect here.** Its actual problems are narrower:

- Undefined helpers (`0` definitions each): `engine_resolve`, `engine_unify`,
  `engine_fresh_var`, `type_Int`, `type_Borrow`, `type_BorrowMut`.
- Line 232 `if has_args:` — `has_args` is a bare undefined identifier used as a
  condition, and the `if base == "Channel":` branch has no `else` on the inner
  `if`, so a `Channel<T>` with no args falls off the end.

## Execution evidence

Probe (control + broken + sentinel), run on the canonical bootstrap binary
`src/compiler_rust/target/bootstrap/simple`. The probe models `check_expr` /
`ast_type_to_inference_type` exactly: `struct Expr { kind: ExprKind }`, one
function matching `e.kind` and one matching `e`, identical arm lists.

```
-- CONTROL (match e.kind:) --
PASS control/IntLit got=IntLit
PASS control/Lambda got=Lambda
PASS control/Call got=Call
PASS control/Other got=FALLBACK
-- BROKEN (match e:) expected-to-be-inert --
FAIL broken/IntLit got=FALLBACK want=IntLit
FAIL broken/Lambda got=FALLBACK want=Lambda
FAIL broken/Call got=FALLBACK want=Call
-- SENTINEL (must FAIL; proves harness reports failures) --
FAIL sentinel got=IntLit want=DELIBERATELY-WRONG
TOTAL_FAILS=4
```

The control passes all four rows, so the harness and the enum dispatch both
work. The broken function fails all three rows — **including `IntLit`, the very
first arm, above any mis-spelled name**. Renaming arms fixes nothing; the
scrutinee is the defect. The sentinel fails as designed, proving the probe can
report a failure at all (guarding against the fall-through-exit-0 trap).

Probe source: `scratchpad/probe_sib.spl` (not committed).

## Decision — file, do not repair

Same reasoning as the `expr_infer` sibling, and it holds harder here:

1. All three are **unwired**. No compilation, no user, no test reaches them.
2. A correct repair is not a scrutinee edit. It requires **authoring ~26
   nonexistent helper functions** across the three files, collapsing
   `Simple`/`Generic` onto the single `Named(text, [Type])` variant, renaming
   arms to real `ExprKind`/`TypeKind` spellings, fixing reversed call sites, and
   supplying behaviour for `ExprKind` concepts the arms assume but the enum does
   not model. That is authoring a new, unverified inference engine under a
   bug-fix label.
3. The `expr_infer` sibling already established the precedent.

If this island is ever revived, the entry criteria are: fix the scrutinees
first, replace both silent fallbacks (`bidirectional.spl:287`,
`module_check.spl:560`) with explicit `Err`, then re-run the probe shape above
as a spec.

## Repro

```bash
/usr/bin/grep -n "match expr:"   src/compiler/30.types/type_system/bidirectional.spl   # 72
/usr/bin/grep -n "match ast_ty:" src/compiler/30.types/type_system/module_check.spl    # 515, 569
/usr/bin/grep -n "^struct Expr"  src/compiler/10.frontend/parser_types_expr.spl        # 204
/usr/bin/grep -n "^struct Type"  src/compiler/10.frontend/parser_types_expr.spl        # 23

# unwired proof — expect exactly the two effect_pass/TypeError lines
/usr/bin/grep -rnE "(use|from|import) +compiler\.types\.type_system" --include='*.spl' src/ test/ \
  | /usr/bin/grep -v "^src/compiler/30.types/type_system/"
```
