# `case Some(<variant>)` over a `Kind?` holding a bare enum: both engines answered wrongly

- **Status:** fixed 2026-11-14 (seed interpreter + HIR/JIT + Rust unit harness)
- **Severity:** P1 (silent wrong value, both engines, no diagnostic)
- **Found by:** PR #9049 (`fdd57145ebe`), listed as "found while writing the
  controls" in `match_on_callable_scrutinee_silently_takes_first_arm_2026-11-14.md`
- **Specs:** `test/01_unit/language/optional_enum_some_variant_match_spec.spl`,
  `src/compiler_rust/compiler/tests/optional_enum_some_variant_match_parity.rs`,
  `interpreter_patterns.rs` unit tests

## Symptom

A `Kind?` parameter, typed `val` or class field holds a bare `Kind` value. Neither
engine Some-wraps at the binding site, so the scrutinee is the raw enum value.

```simple
enum Kind:
    I8
    F32
    Wrap(i64)

fn unq(k: Kind?) -> text:
    match k:
        case Some(I8): "i8"
        case Some(F32): "f32"
        case Some(Wrap(n)): "wrap{n}"
        case None: "none"
        case _: "other"
```

Measured on the base seed (`fdd57145ebe`, aarch64), strict JIT
(`SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1`) and interpreter:

| check | expected | interpreter (base) | JIT (base) |
|---|---|---|---|
| params `unq(F32) unq(I8) unq(Wrap(7)) unq(nil)` | `f32 i8 wrap7 none` | `other other other none` | `i8 i8 i8 none` |
| same, qualified `Some(Kind.X)` | `f32 i8 wrap7 none` | `other other other none` | `i8 i8 i8 none` |
| `Some(x)` binder then `match x` | `b-f32 b-other b-none` | `b-none b-none b-none` | correct |
| typed let `val a: Kind? = Kind.I8` | `i8 wrap5 none` | `other other none` | `f32 i8 none` |
| class field `h.k` | `f32 wrap9 f32 wrap9` | `other other other other` | `i8 f32 i8 i8` |
| scalar `case Some(0)` / `Some(7)` over `i64?` | `zero seven n9 none seven` | correct | `zero zero zero none zero` |
| `case Some("hi")` / `Some(true)` | `hi s:yo none`, `T F none` | correct | `hi hi none`, `T T none` |

The #9049 note "the JIT does match" was true only because its fixture put the
matching arm first: the JIT matched the FIRST `Some(...)` arm for every non-nil
value. Tuple-nested `case (Some(F32), 1):` was already correct on the JIT.

## Root causes

1. **Interpreter** (`interpreter_patterns.rs`, `pattern_matches`, `Pattern::Enum`):
   both flat-Option arms (a bare value is its own `Some` payload) excluded
   `Value::Enum`, and the existing look-through only handled the converse (a real
   `Option::Some(<enum>)` against a user-enum pattern). A bare user enum matched
   no `Some(...)` arm, not even `Some(x)`.
2. **HIR/JIT** (`stmt_lowering.rs` `lower_pattern_condition_stmt` and its
   expression twin in `hir/lower/expr/control.rs`): a top-level builtin-optional
   `Some(p)` lowered to `rt_is_some(subject)` alone and dropped `p`. The nested
   path (`subpattern_condition_typed`, `Ok(Some(..))`) already tested
   presence AND payload.
3. **Rust unit harness**: `run`/`run_err` in `interpreter_patterns.rs` tests called
   `evaluate_module` without clearing thread-local interpreter state, so an earlier
   snippet's `fn code` (`case _: 3` only) answered `code(Kind.I8)` in a later
   snippet. `simple run` evaluates one module per process and never saw it.

## Fix

1. Interpreter: inside the `Value::Enum` branch, a `Some`/`Option`-or-`_` pattern
   over a bare enum whose type is not `Option`/`Result`, whose variant is not
   spelled `Some`/`None`, and whose definition (in `enums` or
   `BLOCK_SCOPED_ENUMS`) declares no `Some`/`None` variant, treats the value as its
   own payload (`enum_declares_option_variant`).
2. HIR: new `optional_some_condition` (control.rs) used by both twins:
   `rt_is_some(subject) && nested_payload_condition("Some", ...)`, which reads the
   slot through the existing dual-representation `payload_slot_expr`. This also
   fixes the scalar-literal rows.
3. Harness: `fresh_interpreter()` (`clear_module_cache` + `clear_interpreter_state`)
   before each snippet. The #9049 workaround assertion (`code(Kind.F32) == 3`) now
   also asserts `code(Kind.I8) == 1`. The pre-existing
   `option_patterns_over_real_option_values_are_not_diagnosed` failure in the same
   module (left 1, right 0 under the default parallel run) also went green with it.

Blast radius: `src/**/*.spl` has 145 `case Some(<non-binder>)` arms (e.g.
`case Some(TokenKind.Comma)` x9, `case Some((lo, hi))`). Under the seed JIT each was
an irrefutable presence test before this change.

## Evidence

CENSUS_PLACEHOLDER

## Review (independent Opus reviewer)

- **P1, fixed before landing:** the first HIR version emitted the payload test
  for every subject. For an UNTYPED subject holding a user enum that declares its
  own `Some` (`enum Opt: Some(i64) | None | Missing`, `fn u(o)`), the raw slot is
  `Opt.Some(5)` itself, so `case Some(5):` became `Opt.Some(5) == 5` and the JIT
  answered `1 1 1` for `u(Opt.Some(5)) u(Opt.Some(6)) u(Opt.Missing)` (base JIT
  `55 55 55`, interpreter `55 1 99`). `optional_some_condition` now emits the
  payload test only for a statically optional subject whose payload type is not
  an enum declaring `Some`/`None`; the rest keep the old presence-only test. The
  spec pins `u(Opt.Some(5)) == 55` on both engines.
- **P3, intended:** the interpreter now matches `case Some(x):` against a bare
  enum in a NON-optional slot too (`fn n(k: Kind)`, `case Some(x): 7` before
  `case I8: 1` answers 7, was 1). The JIT already answered 7, and this is the
  same flat-Option rule the interpreter applies to bare scalars.

## Residuals (open)

- Untyped (ANY) subjects stay presence-only on the JIT: `fn b(k)` with
  `case Some(I8): 1` / `case Some(F32): 2` answers 1 for `Kind.F32` (interpreter
  2). With no slot type, `I8` lowers as a binder. Pre-existing, not changed.
- `Opt?` where `Opt` declares its own `Some`, and the untyped `Opt` case above:
  the JIT still matches the first `Some(...)` arm for any value (interpreter is
  name-keyed). Pre-existing.
- `case Some(x)` over `Ok`/`Err` values still matches on the JIT (interpreter
  refuses). Pre-existing.

- `evaluate_module` does not reset thread-local interpreter state itself; every
  in-process caller must clear it (the integration tests do; the
  `interpreter_patterns` unit harness did not). A same-named function from a
  previous module on the thread wins over the new module's definition.
- Native-build: not measured. It shares the HIR lowering with the JIT.
