# match on a constructor/function scrutinee silently takes its first arm (seed interpreter)

- **ID:** match_on_callable_scrutinee_silently_takes_first_arm_2026-11-14
- **Severity:** P2 (silent wrong value)
- **Status:** fixed (seed interpreter); JIT enum-slot residual fixed
  2026-11-14 (HIR + interpreter call boundary); nested sub-pattern and
  `mod` unit-variant residuals fixed 2026-11-14; JIT method-call arguments open
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
- Nested sub-patterns are checked since 2026-11-14 (see "Nested
  sub-patterns and `mod` unit variants" below).
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

- ~~Nested variant-spelled sub-patterns over a callable payload
  (`case Wrap(I8):`) still bind silently; only the top-level arm is checked.~~
  Fixed 2026-11-14, see below.
- ~~`mod X:` module dicts store unit variants as `EnumVariantConstructor`
  (`interpreter_eval.rs`, found by review). A match on such a value now
  errors loudly instead of answering silently, but the encoding is wrong.~~
  Fixed 2026-11-14, see below.

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

"After" columns are from the final binary of this change. Every refused row
exits 1 on all three lanes: strict JIT, non-strict JIT, and interpreter.

| fixture | strict JIT before | after: strict JIT / non-strict JIT / interp |
|---|---|---|
| `kind_name(Vec4f)` (local class), `case _` | `other`, rc 0 | refused (HIR) / refused / refused (call boundary) |
| `kind_name(Vec4f)` (`use std.simd.{Vec4f}`, the real struct) | `other`, rc 0 | refused on all three |
| `kind_name(helper)` (fn), no wildcard | `0`, rc 0 | refused on all three |
| `kind_name(Kind)` (the enum type itself) | `other`, rc 0 | refused on all three |
| `kind_name(k: Vec4f)` (named arg) | `other`, rc 0 | refused on all three |
| callee declared after caller | `other`, rc 0 | refused on all three |
| callee imported from another module | `other`, rc 0 | refused on all three |
| `kind_opt(Vec4f)`, `k: Kind?`, `case Some(I8):` | **`i8`, rc 0** (interp also `i8`) | refused on all three |
| `val k: Kind = Vec4f` | `other`, rc 0 | refused on all three (interp: typed-binding check) |
| `val k: Kind? = Vec4f`, `case Some(I8):` | `i8`, rc 0 (interp `i8`) | refused on all three |
| `Box(k: Vec4f)`, field `k: Kind` (same file) | `other`, rc 0 | refused (HIR) / refused / match-arm error (interp has no field check) |
| `n.name(Vec4f)`, method param `k: Kind` (same-file class) | `other`, rc 0 | refused on all three |
| real enum values (control) | correct | unchanged on all three |

On a HIR lowering error, non-strict JIT demotes the module to the
interpreter, which refuses the same value at the call or binding boundary.

Fix:

- HIR (`hir/lower/expr/calls.rs` `reject_callable_for_enum_slot`):
  - Fires when the slot type is a user enum (also through `T?`; never
    `Option`/`Result`) and the value is either typed `Function` or is a bare
    type-name reference. A class name used as a value lowers to
    `Global("Vec4f")` typed as struct `Vec4f`, which is what this matches.
  - A `::` variant path is never treated as a type reference.
  - Called on:
    - the final slot-ordered call arguments, using the callee's type, or the
      new `fn_param_type_names` table when the callee is declared after its
      caller;
    - typed `val`/`var`;
    - field initialisers of a class declared in the same file, under the same
      soundness gate as the unknown-field check;
    - positional method arguments on a receiver class/struct declared in the
      same file, via the new `method_param_type_names` table. A row that
      same-named owners disagree on is left unchecked.
  - Struct-typed locals and erased slots keep the old contract, because the
    seed's aggregate typing is not authoritative.
- Interpreter (`interpreter_call/core/arg_binding.rs`
  `reject_callable_for_enum_param`):
  - Called through the 4-argument `validate_unit!` at parameter binding, and
    at typed `val`/`var` (`interpreter/node_exec.rs`).
  - Refuses a `Constructor`/`Function`/`Lambda`/`BlockClosure`/
    `NativeFunction`/`EnumType`/`TraitType` value whose declared `Kind`/`Kind?`
    names a known enum.
  - `EnumVariantConstructor` is not refused, because module dicts store unit
    variants that way (residual above).
  - The value's shape is tested first, so data arguments never pay the
    enum-table lookup.

Open after this fix:

- Method arguments that are named, or whose receiver class is declared in
  another module, are not checked in HIR. The JIT still runs those silently.
  The interpreter refuses them only when it actually runs the call, that is in
  interpret mode or after a demotion caused by something else.
- Field initialisers:
  - HIR: imported-struct field initialisers are not checked, for the same
    reason the unknown-field check skips them.
  - Interpreter: no field-init check at all, so only the match-arm error
    fires.
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
  passed to such a trait-typed parameter would now be refused. The census
  below found none.
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

## Nested sub-patterns and `mod` unit variants (residuals, fixed 2026-11-14)

Measured on the base seed (`ff993c1134d`, aarch64, interpreter):

| fixture | before | after |
|---|---|---|
| `name_of(Wrap.W(Vec4f))`, `case W(I8):` first | `i8`, rc 0 | error, rc 1 |
| `name_of(Some(helper))`, `case Some(I8):` | `i8`, rc 0 | error, rc 1 |
| `mod X: enum Kind: I8 F32`, `print(X.F32)` | `<enum_variant_constructor>` | `Kind::F32` |
| `X.F32 == X.F32` | `false` | `true` |
| `match X.F32: case I8 / case F32` | error (callable scrutinee) | `f32` |
| controls: real `W(Kind.F32)`, `W(f)`, `W(I8 \| f)`, `W(I8) \| _`, `X.Pay`, `X.LIMIT`, `X.twice(4)` | correct | unchanged |

Nested fix (`interpreter_patterns.rs`):

- `match_arm_matches` enters an arm mode (thread-local, restored by a drop
  guard, so it never leaks into `val`/`if val`/`for` destructuring, which
  keep binding).
- In arm mode, `pattern_matches` treats a variant-spelled identifier or a
  non-`Some`/`None`/`Ok`/`Err` enum-variant node reached with a callable or
  type value as a non-match and records it. The value shape is tested first,
  so data values never read the thread-local.
- If the whole arm then fails, `match_arm_matches` raises
  `invalid pattern: match payload is a constructor value <constructor:Vec4f>,
  not an enum value; sub-pattern `I8` can never match it`. An alternative that
  does match (`W(I8 | f)`, `W(I8) | _`) still wins, as at the top level.

`mod` fix (`interpreter_eval.rs`, `Node::ModDecl`): unit variants go into the
module dict as `Value::Enum { payload: None }`; payload variants stay
`EnumVariantConstructor`. Same rule as `Enum.Variant` in
`interpreter/expr/calls.rs`.

Still open, pre-existing, not changed here (seen while writing the fixtures):

- A `mod X:` dict is not visible inside function bodies (`fn main(): X.F32`
  gives `variable X not found`). Only module-level code can use it.
- `X.Pay(3)` (calling a payload variant through the dict) fails with
  `method Pay not found on type dict`.
- A function inside `mod X:` cannot name its sibling variants (`F32` gives
  `variable F32 not found`), and `X.Kind` is not in the dict.
- `reject_callable_for_enum_param` still admits `EnumVariantConstructor`; now
  that no unit variant uses that encoding it could be refused. Not tightened.

## Census (false-positive sweep)

The census used a binary in which both checks logged and passed instead of
erroring. It ran each file once with `SIMPLE_EXECUTION_MODE=jit run`:

- **Scope:** every `*_spec.spl` whose path names enum/match/pattern/variant
  (413 files), plus a sample of every 180th other spec (120 files).
- **Both checks were exercised.** Every file demoted at least once to the
  interpreter (`fallback>=1` on all rows), so the census covered the HIR check
  during lowering and the interpreter parameter check during execution.
- **App entries:** also lowered under the JIT were `src/app/cli/main.spl`
  (lowering stopped early on an unrelated `struct 'ANY' field 'route'` error),
  `src/app/mcp/main.spl` (per-module JIT, many modules) and
  `src/app/lsp/main.spl`.
- **Result: 0 hits** (exact counts are in the PR).
- **Not covered by that binary:** the method-argument check and the
  interpreter typed-`val` check were added after the census binary was built.
  For typed `val`, a static sweep of every
  `val/var x: <Enum>[?] = <Capitalized identifier>` in src/test/examples
  (2,979 enum names, 2,483 typed single-identifier lets) found 0 sites other
  than `= None`. The method-argument check is gated to positional calls on
  same-file classes.

## Regression

- `test/01_unit/language/enum_param_rejects_callable_value_spec.spl` (strict
  JIT and interpreter, through `SIMPLE_BINARY`/`bin/simple`)
- Rust: `hir::lower::tests::expression_tests::callable_or_type_value_never_lowers_into_an_enum_slot`,
  `interpreter_patterns::tests::callable_bound_to_enum_parameter_is_refused_at_the_call`.
  The #9042 fixtures below now pass the value through an untyped `code(k)` /
  `kind_name(k)` parameter, since a typed one refuses it before the match.
- `test/01_unit/language/match_callable_scrutinee_no_silent_first_arm_spec.spl`
  (runs fixtures through `SIMPLE_BINARY`/`bin/simple` in interpreter mode)
- `test/01_unit/compiler/95.interp/interpreter/match_nested_callable_and_mod_unit_variant_spec.spl`
  (nested and `mod` residuals; red 3/5 on the base seed, green 5/5 after)
- Rust: `interpreter_patterns::tests::nested_variant_sub_pattern_over_callable_payload_is_refused`
- Rust: `interpreter_patterns::tests::{match_on_constructor_value_errors_instead_of_taking_first_arm,
  match_on_function_value_errors_instead_of_taking_first_arm,
  statement_and_val_match_on_constructor_value_error_too,
  earlier_binder_or_wildcard_arm_still_wins_over_callable,
  variant_spelled_arms_against_callables_refuse_directly}`
