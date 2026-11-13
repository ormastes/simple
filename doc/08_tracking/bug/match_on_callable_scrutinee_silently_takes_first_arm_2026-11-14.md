# match on a constructor/function scrutinee silently takes its first arm (seed interpreter)

- **ID:** match_on_callable_scrutinee_silently_takes_first_arm_2026-11-14
- **Severity:** P2 (silent wrong value)
- **Status:** fixed (seed interpreter); JIT residual filed below
- **Found by:** PR #9002 (`e4300d7920b`), left open in
  `opencl_backend_contract_plug_notfound_and_enum_variant_class_shadow_2026-11-13.md`

## Symptom

A `match` whose scrutinee is a constructor, function or type value (not an
enum value) took its first variant-spelled arm and exited 0:

```simple
class Vec4f:
    x: i64
enum Kind:
    I8
    F32
fn kind_name(k: Kind) -> text:
    match k:
        case I8: "i8"
        case F32: "f32"
        case _: "other"
fn main():
    print(kind_name(Vec4f))   # printed "i8", rc 0
```

This is what turned PR #9002's misresolution (`MirTypeKind.Vec4f` ->
`<constructor:Vec4f>` inside a fn body) into the OpenCL backend emitting
`char` instead of failing. #9002 fixed the name resolution; this fixes the
silent fallthrough.

## Root cause

`case I8:` parses as `Pattern::Identifier("I8")`. `pattern_matches`
(`src/compiler_rust/compiler/src/interpreter_patterns.rs`) only treats a bare
variant-spelled identifier as a variant test when the value is a
`Value::Enum`; for every other value it is an irrefutable binding. A
`Value::Constructor` therefore bound `I8` and matched arm 1.

## Fix

New `match_arm_matches` in `interpreter_patterns.rs`, called by all four
interpreter match-arm loops (`interpreter/expr/control.rs` `Expr::Match`,
`interpreter_control.rs` `exec_match_core`, and the two `Node::Match` loops
in `interpreter_call/block_execution.rs`). When the scrutinee is a
`Constructor`, `Function`, `Lambda`, `BlockClosure`, `NativeFunction`,
`EnumType`, `EnumVariantConstructor` or `TraitType` value and the reached
arm is variant-shaped (a variant-spelled bare identifier, or an enum-variant
pattern other than `Some`/`None`/`Ok`/`Err`, seen through `|` and `: T`),
the match raises:

```
invalid pattern: match scrutinee is a constructor value <constructor:Vec4f>,
not an enum value; arm `case I8:` can never match it
```

Scope is deliberate:

- Only match arms. `val`/`if val`/`while val`/`for` binding still uses
  `pattern_matches`, where `val Handler = some_fn` is a legitimate binding.
- An earlier arm that matches (`case _:`, a lowercase binder) still wins; the
  error fires only when a variant-shaped arm is reached. An arm with a real
  catch-all alternative (`case _ | I8:`, `case f | I8:`) still matches.
- Nested sub-patterns are not checked (`case Wrap(I8):` with a callable
  payload still binds); filed as a residual below.
- A capitalized arm over plain data (`case WS_OPCODE_TEXT:` on an `i64`)
  keeps binding, as pinned by `bare_case_ident_variant_pattern_spec`.
- `case Some(f):` over a callable keeps the flat-Option binding.

## Engine parity (measured 2026-11-14, aarch64, seed built from
`228560191e0`)

| fixture | interpret (before) | interpret (after) | JIT strict |
|---|---|---|---|
| constructor scrutinee, with `case _:` | `i8`, rc 0 | error, rc 1 | `other`, rc 0 (wildcard taken) |
| function scrutinee, no wildcard | `i8`, rc 0 | error, rc 1 | `match expression exhausted`, abort rc 134 |
| real enum + capitalized binder over i64 (control) | `f32` / `bound 7` | same | same |

The JIT never takes the first arm (its variant test is a tag compare), so the
reported bug is interpreter-only. The JIT residual is that
`kind_name(Vec4f)` (a constructor passed for a `Kind` parameter) compiles at
all and then falls to `case _:` silently; that is a missing call-argument
type check, not a pattern-matcher defect. Filed as the open residual below.
Native-build: not measured; `SIMPLE_BOOTSTRAP=1 native-build` of the fixture hit the 900 s cap (rc 124) while interpreting the self-hosted compiler. It shares the HIR/MIR match lowering with the JIT, so the JIT row is the expected native behaviour, unproven.

## Residuals (open)

- Nested variant-spelled sub-patterns over a callable payload
  (`case Wrap(I8):`) still bind silently; only the top-level arm is checked.
- `mod X:` module dicts store unit variants as `EnumVariantConstructor`
  (`interpreter_eval.rs`, found by review). A match on such a value now
  errors loudly instead of answering silently, but the encoding is wrong.

- JIT/HIR: a class constructor passed where an enum parameter is declared is
  not rejected at compile time; the match then takes `case _:` silently.
- Interpreter statement-form `match` with no matching arm (and no wildcard)
  returns `Control::Next` silently (`exec_match_core` tail), unlike the
  expression form, which raises "match expression exhausted". Not changed
  here: it is the long-standing statement semantics and needs an owner
  decision.

## Regression

- `test/01_unit/language/match_callable_scrutinee_no_silent_first_arm_spec.spl`
  (runs fixtures through `SIMPLE_BINARY`/`bin/simple` in interpreter mode)
- Rust: `interpreter_patterns::tests::{match_on_constructor_value_errors_instead_of_taking_first_arm,
  match_on_function_value_errors_instead_of_taking_first_arm,
  statement_and_val_match_on_constructor_value_error_too,
  earlier_binder_or_wildcard_arm_still_wins_over_callable,
  variant_spelled_arms_against_callables_refuse_directly}`
