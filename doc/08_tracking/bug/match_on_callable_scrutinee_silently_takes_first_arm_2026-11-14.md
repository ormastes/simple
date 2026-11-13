# match on a constructor/function scrutinee silently takes its first arm (seed interpreter)

- **ID:** match_on_callable_scrutinee_silently_takes_first_arm_2026-11-14
- **Severity:** P2 (silent wrong value)
- **Status:** fixed (seed interpreter); JIT enum-slot residual fixed
  2026-11-14 (HIR + interpreter call boundary); JIT method-call arguments open
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

- ~~JIT/HIR: a class constructor passed where an enum parameter is declared is
  not rejected at compile time; the match then takes `case _:` silently.~~
  Fixed 2026-11-14, see "Enum-slot admission" below. Method-call arguments
  remain open (listed there).
- Interpreter statement-form `match` with no matching arm (and no wildcard)
  returns `Control::Next` silently (`exec_match_core` tail), unlike the
  expression form, which raises "match expression exhausted". Not changed
  here: it is the long-standing statement semantics and needs an owner
  decision.

## Enum-slot admission (JIT residual, fixed 2026-11-14)

Re-measured on the base seed (`7423d7d5bdb`, aarch64), strict JIT
(`SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1`). The doc's earlier row
"function scrutinee, no wildcard: abort rc 134" did not reproduce: it printed
`0` with rc 0, which is worse.

| fixture | strict JIT before | strict JIT after | interpreter after |
|---|---|---|---|
| `kind_name(Vec4f)` (local class), `case _` | `other`, rc 0 | HIR error, rc 1 | call-boundary error |
| `kind_name(Vec4f)` (`use std.simd.{Vec4f}`, the real struct) | `other`, rc 0 | HIR error | call-boundary error |
| `kind_name(helper)` (fn), no wildcard | `0`, rc 0 | HIR error | call-boundary error |
| `kind_name(Kind)` (the enum type itself) | `other`, rc 0 | HIR error | call-boundary error |
| `kind_name(k: Vec4f)` (named arg) | `other`, rc 0 | HIR error | call-boundary error |
| callee declared after caller | `other`, rc 0 | HIR error | call-boundary error |
| callee imported from another module | `other`, rc 0 | HIR error | call-boundary error |
| `kind_opt(Vec4f)`, `k: Kind?`, `case Some(I8):` | **`i8`, rc 0** (interp also `i8`) | HIR error | call-boundary error |
| `val k: Kind = Vec4f` | `other`, rc 0 | HIR error | match-arm error (no let check in interp) |
| `Box(k: Vec4f)`, field `k: Kind` (same file) | `other`, rc 0 | HIR error | match-arm error |
| `n.name(Vec4f)`, method param `k: Kind` | `other`, rc 0 | **`other`, rc 0 (open)** | call-boundary error |
| real enum values (control) | correct | unchanged | unchanged |

Non-strict JIT: a HIR lowering error demotes the module to the interpreter,
which now refuses the same calls at the call boundary, so no lane runs the
match with a callable typed as an enum (method arguments excepted).

Fix:

- HIR (`hir/lower/expr/calls.rs` `reject_callable_for_enum_slot`): a slot whose
  type is a user enum (also through `T?`; never `Option`/`Result`) refuses a
  value typed `Function`, or a bare type-name reference (`Global("Vec4f")`
  typed as struct/enum `Vec4f`, which is how a class name used as a value
  lowers). Called on the final slot-ordered call arguments (callee type, or a
  new `fn_param_type_names` table for a callee declared after its caller),
  typed `val`/`var`, and same-file class field initialisers (same soundness
  gate as the unknown-field check). Struct-typed locals and erased slots keep
  the old contract: the seed's aggregate typing is not authoritative.
- Interpreter (`interpreter_call/core/arg_binding.rs`
  `reject_callable_for_enum_param`, via the 4-argument `validate_unit!`): a
  `Constructor`/`Function`/`Lambda`/`BlockClosure`/`NativeFunction`/
  `EnumType`/`TraitType` value bound to a `Kind`/`Kind?` parameter whose name
  is a known enum is a type mismatch. `EnumVariantConstructor` is not refused
  (module dicts store unit variants that way, residual above). The value
  shape is tested first so data arguments never pay the enum-table lookup.

Open after this fix:

- JIT method-call arguments (`n.name(Vec4f)`): method calls lower through
  dynamic dispatch with no resolved parameter list at the HIR site, and
  same-bare-name receiver types make a guess unsafe.
- Imported-struct field initialisers (`Box` declared in another module) are
  not checked, for the same reason the unknown-field check skips them.
- Narrower gaps the review listed (P2, not fixed): a slot written as
  `Option<Kind>` (only `Kind?` is unwrapped); parameter default values and
  injected values in the interpreter (3-argument `validate_unit!`); a
  function declared after its use passed as a value (typed by its return type,
  not `Function`); a named-argument call whose callee has no names contract
  (skipped, not mis-checked). For a callee declared after its caller the slot
  type name is resolved in the caller's scope, so a same-named non-enum type
  in another flattened module could be chosen.
- Interpreter false-positive risk (P2): the interpreter's enum table is keyed
  by bare name and the tree has names that are both a trait and an enum
  (`Backend`, `DebugTarget`, `Display`, `EventBackend`, `Transport`). A lambda
  passed to such a trait-typed parameter would now be refused. None was found
  by the census below.
- Self-hosted compiler: `infer_function_call`
  (`src/compiler/30.types/type_infer/inference_expr_calls.spl`) already checks
  each argument with `InferMode.Check(expected_param)` and unifies the call.
  Whether a class name used as a value synthesizes to a type that `unify`
  rejects against an enum is unproven: no self-hosted full-CLI binary is
  deployed on this host, and running the compiler from source hit the 900 s
  cap before. Not changed.
- Found while writing the controls (pre-existing, not caused by this change):
  - Interpreter `fn opt(k: Kind?)` called with `Kind.F32` does not match
    `case Some(F32):` (answers the wildcard); the JIT matches it. Engine
    divergence on `T?` parameters receiving a bare enum value.
  - The Rust unit harness (`evaluate_module`, `main = code(Kind.I8)`) takes
    `case _:` for a real `Kind.I8`, even through an untyped parameter, while the
    CLI answers the `I8` arm. Harness-only divergence; not investigated.

## Regression

- `test/01_unit/language/enum_param_rejects_callable_value_spec.spl` (strict
  JIT and interpreter, through `SIMPLE_BINARY`/`bin/simple`)
- Rust: `hir::lower::tests::expression_tests::callable_or_type_value_never_lowers_into_an_enum_slot`,
  `interpreter_patterns::tests::callable_bound_to_enum_parameter_is_refused_at_the_call`.
  The #9042 fixtures below now pass the value through an untyped `code(k)` /
  `kind_name(k)` parameter, since a typed one refuses it before the match.
- `test/01_unit/language/match_callable_scrutinee_no_silent_first_arm_spec.spl`
  (runs fixtures through `SIMPLE_BINARY`/`bin/simple` in interpreter mode)
- Rust: `interpreter_patterns::tests::{match_on_constructor_value_errors_instead_of_taking_first_arm,
  match_on_function_value_errors_instead_of_taking_first_arm,
  statement_and_val_match_on_constructor_value_error_too,
  earlier_binder_or_wildcard_arm_still_wins_over_callable,
  variant_spelled_arms_against_callables_refuse_directly}`
