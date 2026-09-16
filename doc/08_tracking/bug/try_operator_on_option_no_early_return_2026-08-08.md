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

Failures on the `None` path:

1. **No early return — this is the load-bearing finding.** `SIDE_EFFECT_RAN`
   fires after `?` on a `None`; the function body continues as though the Option
   were present. Unambiguous and reproducible.
2. **The caller gets no recognizable `None`.** The `match` produced a blank line
   rather than `none_case=NONE`. NOT DISAMBIGUATED: that blank is consistent
   with either (a) neither arm matching, so the `match` fell through and printed
   nothing, or (b) `case Some(v)` matching with an empty/garbage `v`. Both are
   wrong and neither changes the fix direction, but which one it is was not
   determined. Do not cite this as "matches neither variant" without re-probing;
   cite point 1, which stands on its own.

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

## Related, also unguarded: `?` in a function that does not return Result

Found in the same review. `lower_try` emits
`HirStmt::Return(subject_ref)` typed `subject_ty` regardless of the enclosing
function's declared return type, and nothing diagnoses the mismatch:

```simple
fn inner(bad: bool) -> Result<i64, text>:
    if bad:
        return Err("boom")
    return Ok(42)

fn not_result(bad: bool) -> i64:      # NOT a Result
    val n = inner(bad)?
    return n + 1

fn main():
    print("ok="  + not_result(false).to_text())
    print("err=" + not_result(true).to_text())
```

Observed (post-fix seed, exit code 0, no diagnostic):

```
ok=43
err=3012356214401
```

`3012356214401` is the raw `Err`-tagged enum handle escaping as an `i64` from a
function declared `-> i64`.

**Framing: pre-existing hole, not a regression.** Before `a59575dfde3` this
returned the unwrapped payload — also wrong. The change swapped one silent wrong
value for another and additionally made it a *type* violation. Either way `?` in
a non-`Result` function should be a compile-time error; today it silently
miscompiles. Filed here rather than separately because the fix belongs in the
same `lower_try` type-dispatch work as the Option case above.

---

## Triage re-verification 2026-08-17 (c_mir lane, classified by CONTENT not SHA)

**Governing fact for every 50.mir-attributed row:** nothing runnable on this
host executes `src/compiler/50.mir/**.spl`. `bin/simple` resolves to
`bin/release/x86_64-unknown-linux-gnu/simple` (59536728 bytes, mtime
2026-08-16 22:59), whose own `--version` banner states it is a Rust
**bootstrap seed**; it has its own Rust MIR/JIT/native pipeline and never reads
`src/compiler/**.spl` for compilation logic. `bin/release/simple` is the
2181-byte refusing production-guard wrapper, and no stage2/stage3 self-hosted
binary exists under `build/bootstrap/`. Therefore any evidence in this doc
phrased as "reproduced on `bin/simple`" is evidence about the **seed**, not
about 50.mir, and the runtime claim here can only be closed by a full
self-hosted bootstrap (not run: the user's bootstrap is live and
`build/bootstrap/**` is off-limits). Rows were therefore classified by
grepping current source.

**Verdict: STILL PRESENT, but MIS-ATTRIBUTED — the defect is in the Rust SEED, not 50.mir.**

Confirmed live in current seed source at
`src/compiler_rust/compiler/src/hir/lower/expr/control.rs:2302-2319` —
`result_like_payload_type(subject_ty).unwrap_or(TypeId::ANY)` followed by an
unconditional hash of the literal `"Err"` into `rt_enum_check_discriminant`, with
no Optional branch anywhere before it. An Option never carries that
discriminant, so `?` never early-returns. The 50.mir counterpart IS fixed (see
`native_try_op_on_option_silent_wrong_2026-07-14.md`). Note also that
`scripts/check/check-try-operator-error-propagation.shs` reported
`PASS — 3 engine(s) checked: default,interpret,jit` on 2026-08-17, but that gate
does NOT cover this row: its own header at line 37 reads "SCOPE — Result ONLY.
`?` on an Option is a SEPARATE, STILL-OPEN defect". Recommend re-attributing this
row to `hir/lower/expr/control.rs`.
