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

Seeds: base `fdd57145ebe`, fix = this change; after merging release/1.0.0 the
merged seed was rebuilt and everything below except the census was re-run on it
(aarch64).

- Red -> green: `optional_enum_some_variant_match_spec.spl` is 1/7 on the base
  seed (6 failed) and 7/7 on the merged seed.
- Neighbours on the merged seed, all green at their full counts:
  `match_callable_scrutinee_no_silent_first_arm_spec` 3/3,
  `match_nested_callable_and_mod_unit_variant_spec` 5/5,
  `enum_param_rejects_callable_value_spec` 10/10, `inline_mod_block_spec` 12/12.
- Rust: `cargo test -p simple-compiler --release --lib interpreter_patterns` 41
  passed, `--test optional_enum_some_variant_match_parity` 2 passed.
- Census (pre-merge seeds, serial, each spec through `simple test` and through
  `SIMPLE_EXECUTION_MODE=jit simple run`): the 535 specs under `test/` whose
  path matches `enum|match|pattern|option`. Base: 428 runner-green, 426
  JIT-green. Fix: 534 of 535 rows byte-identical to base (same verdict line, JIT rc and pass/fail counts), 0 base-green rows red.
  The one differing row, `tuple_pattern_binder_and_if_match_type_spec.spl`
  (JIT 5/5 base, 0/5 fix in the census), did not reproduce: 10/10 JIT runs green
  on the fix seed and 10/10 on the base seed, so it is recorded as a one-off
  under host load, not a regression.

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

## Review after merging release/1.0.0 (independent Fable reviewer, diff only)

No P0/P1. Confirmed by reading: the look-through fires only on `Value::Enum`, so
it cannot bypass or double-record the #9058 callable refusal (probe:
`g(Box.Hold(Kind.Wrap))` against `case Some(Hold(I8))` still raises `invalid
pattern` in the interpreter); arm bindings are fresh per arm; the HIR subject is
a local, so nothing is evaluated twice. P2 findings, recorded as residuals below:
the `Tok?` case where the payload enum declares `None`, the definition-visibility
dependence of `enum_declares_option_variant`, and JIT coverage gaps. The
own-`Some` test now also pins `u(Opt.Some(6)) u(Opt.Missing) == 1 99` on the
interpreter.

## Residuals (open)

- `case Some(x)` over a NON-optional `k: Kind` (or a user `MyRes.Ok(1)`) now
  matches in the interpreter (P3 above; the JIT always did). Plain variant arms
  over `k: Kind` are unchanged and pinned by the spec. The matcher has no slot
  type, so this cannot be gated there; a type-check diagnostic is the real fix.
- An optional whose payload enum declares its own `None`/`Some`
  (`enum Tok: None | Num(i64)`, `fn f(t: Tok?)`, `case Some(Num(1))` /
  `case Some(Num(n))` / `case _`): both engines opt out of the fix, so
  `f(Tok.Num(5))` still answers 9 (interpreter) and 1 (JIT). Not measured, from
  review.
- `enum_declares_option_variant` reads `enums` and `BLOCK_SCOPED_ENUMS` only. An
  enum declaring `Some` that is visible through neither would let
  `Opt.Missing` match `case Some(x)`. A `mod M:` enum was probed and is found
  (`u(M.Opt.Some(5)) u(M.Opt.Some(6)) u(M.Opt.Missing)` = `55 1 99`); imported
  enums were not probed.
- No JIT spec coverage for `Some(I8) | Some(F32)`, guards, f64 literals,
  top-level `Some((0, b))` / `Some(Point(0, y))`, or `Option<Kind>` spelling;
  `Option<(i64, i64)>` stays presence-only on the JIT.

- Untyped (ANY) subjects stay presence-only on the JIT: `fn b(k)` with
  `case Some(I8): 1` / `case Some(F32): 2` answers 1 for `Kind.F32` (interpreter
  2). With no slot type, `I8` lowers as a binder. Qualified `Some(Kind.I8)` over an
  untyped subject is presence-only too (reviewer probe: JIT `1 1 1 1 5`,
  interpreter `1 2 2 3 5`), because the P1 guard keeps ANY subjects on the old
  test. Base-identical, not a regression; engines still disagree here.
- `Opt?` where `Opt` declares its own `Some`, and the untyped `Opt` case above:
  the JIT still matches the first `Some(...)` arm for any value (interpreter is
  name-keyed). Pre-existing.
- `case Some(x)` over `Ok`/`Err` values still matches on the JIT (interpreter
  refuses). Pre-existing.

- `evaluate_module` does not reset thread-local interpreter state itself; every
  in-process caller must clear it (the integration tests do; the
  `interpreter_patterns` unit harness did not). A same-named function from a
  previous module on the thread wins over the new module's definition.
- Triple-qualified patterns over a `mod`-scoped enum (`case M.K.A:` for
  `mod M: enum K`) match nothing in the interpreter, with or without `Some(...)`
  (`d(M.K.B) d(M.K.A) d(M.K.P(4))` answers `other other other`); the strict JIT
  refuses the module (`struct 'ANY' field 'B'`). Unqualified `case Some(A):` /
  `Some(P(n))` over `M.K?` is correct (`b a p4 none`). Pre-existing, belongs to the
  `mod X:` lane (#9074).
- JIT: a callable payload under a nested variant pattern
  (`g(Box.Hold(Kind.Wrap))` against `case Some(Hold(Wrap(n)))`) prints
  `h-wrapnil`; the interpreter raises the #9058 `invalid pattern` error, also
  through the new look-through. Pre-existing JIT gap.
- Native-build: not measured. It shares the HIR lowering with the JIT.
