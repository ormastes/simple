# `?` on an Option neither early-returns nor produces a matchable value

- **Status:** OPEN
- **Found:** 2026-08-08, during adversarial review of `a59575dfde3`
- **Component:** Rust seed HIR lowering — `lower_try`,
  `src/compiler_rust/compiler/src/hir/lower/expr/control.rs:2194`
- **Severity:** High. Silent wrong control flow + a value that matches no
  variant. No diagnostic, no crash, exit code 0.
- **Related:** `try_operator_early_return_matches_neither_ok_nor_err_2026-08-07.md`
  (the `Result` half, fixed by `a59575dfde3`). This is the **Option** half of the
  same family and is **still open**.

## Summary

`a59575dfde3` fixed `?` for `Result` by binding the subject to a `LetIn` temp,
testing the hashed `"Err"` discriminant via `rt_enum_check_discriminant`, and
early-returning the whole `Err`-tagged value.

That discriminant is computed from the **string literal `"Err"`,
unconditionally**, with no branch on the subject's type:

```rust
// control.rs:2225 — hashed "Err" discriminant, emitted for EVERY `?`
let err_disc: i64 = {
    let mut hasher = DefaultHasher::new();
    "Err".hash(&mut hasher);
    (hasher.finish() & 0xFFFFFFFF) as i64
};
```

An `Option` has variants `Some`/`None`. Neither hashes to `hash("Err")`, so
`rt_enum_check_discriminant` is **false for both**, the early-return branch is
never taken, and control falls through to `rt_enum_payload(tmp)` on a `None`.

## Reproduction

Probe (also usable verbatim to promote the assertion into
`scripts/check/check-try-operator-error-propagation.shs` once fixed):

```simple
fn boxed_opt(bad: bool) -> text?:
    if bad:
        return None
    return Some("v")

fn use_opt(bad: bool) -> text?:
    val p = boxed_opt(bad)?
    print("  SIDE_EFFECT_RAN")
    return Some("got:" + p)

fn main():
    print("none_case START")
    val a = use_opt(true)
    match a:
        case Some(v): print("none_case=SOME:" + v)
        case None: print("none_case=NONE")
    print("some_case START")
    val b = use_opt(false)
    match b:
        case Some(v): print("some_case=SOME:" + v)
        case None: print("some_case=NONE")
```

Observed on the **post-fix** deployed seed (`bin/simple run`, exit code 0):

```
none_case START
  SIDE_EFFECT_RAN
                      <- blank: the match printed NOTHING
some_case START
  SIDE_EFFECT_RAN
some_case=SOME:got:v
```

Two distinct failures on the `None` path:

1. **No early return.** `SIDE_EFFECT_RAN` fires after `?` on a `None`. The
   function body continues as though the Option were present.
2. **The result matches neither variant.** Both `case Some(v)` and `case None`
   fail to match, so the `match` prints nothing at all — the same
   "matches neither" shape as the original `Result` defect.

The success path is correct.

## Why the fix's parity claim is wrong

`a59575dfde3`'s doc comment states the new shape "mirrors ... the pure-Simple
`lower_try_expr` in `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`".
It does not. The pure-Simple lowering has a dedicated
`case HirTypeKind.Optional(inner)` arm, and its docstring spells out that Option
needs handling the seed's version has no equivalent of:

- presence is tested via `rt_is_some` / `rt_enum_discriminant`, not a hashed
  `"Err"` constant;
- **two** physical Option representations must be handled — the flat-nullable
  ABI (`val x: i64? = 3`, whose raw word IS its own payload) and the boxed
  `Some(v)`/`None` enum ABI — disambiguated at runtime because
  `rt_enum_discriminant` returns `-1` for a non-registered handle;
- on absence the raw nil local must be promoted to the canonical enum-id-1
  `None` handle before the early return, or the branch bypasses the enclosing
  function's typed-return promotion.

The seed's `lower_try` does none of this. The parity claim in the comment should
be corrected to say it mirrors the pure-Simple lowering **for `Result` only**.

## Fix direction

Branch on the subject type in `lower_try`, as the pure-Simple lowering does:

- **Result** — current shape is correct, keep it.
- **Option** — test presence (not a hashed `"Err"`), early-return a canonical
  `None` handle on absence, and extract the payload on the boxed/flat lanes as
  `lower_try_expr` documents.

Note the discriminant-convention split this codebase already carries: boxed
`Some`/`None` built by `lower_enum_construct_named` use **positional**
discriminants (`Some=0`, `None=1`), while `Result`'s `Ok`/`Err` use **hashed**
variant names (`variant_disc`, `codegen/instr/result.rs:13`). Whatever presence
test is chosen must be correct for the convention actually used at construction;
the pure-Simple lowering routes via `rt_enum_discriminant` specifically to avoid
`rt_is_none`'s legacy hashed constant, which does not match what construction
assigns.

## Guard status

Not guarded. `scripts/check/check-try-operator-error-propagation.shs` covers the
`Result` case only and deliberately excludes Option so it stays green on
landing — promote the probe above into it as part of the fix.

A `describe`/`it`/`expect` spec **cannot** guard this: the spec DSL executes
example bodies through a path that never reaches the JIT `lower_try` lowering,
which is why `test/01_unit/try_operator_error_propagation_spec.spl` passes
identically on broken and fixed seeds. Use the check script.
