# Bug: `expect(a == b).to_equal(false)` false-fails when a != b

**Date:** 2026-06-30
**Severity:** Medium — false-RED on specs that assert inequality via the
`expect(<comparison>).to_equal(<bool>)` idiom (library/code is correct).
**Component:** Rust seed BDD runner — infix-comparison handler
(`interpreter_call/bdd.rs` ~L815-849) vs matcher (`interpreter_method/mod.rs`).

## Symptom

```simple
expect("aaa" == "bbb").to_equal(false)   # FAILS, should pass
expect("aaa" == "aaa").to_equal(true)    # passes
expect("aaa").to_not_equal("bbb")        # passes (idiomatic)
```

`crypto/tls12_prf_kat_spec` uses `expect(sha256 == sha384).to_equal(false)` to
assert the two PRFs differ. The crypto is CORRECT (SHA-256 master_secret
`96687db2…` != SHA-384 `f0e19b80…`; `hmac_sha384_bytes` verified to vary with
input). The test fails purely on this harness idiom.

## Root cause

`expect(<Expr::Binary ==>)` takes the infix path in `bdd.rs`: it evaluates the
comparison and, when `!matched` (a != b), **eagerly sets the hard
`BDD_EXPECT_FAILED` flag** (L838-848), then returns `Bool(matched)`. The trailing
`.to_equal(false)` matcher runs on `Bool(false)`, matches, but the matcher only
ever *sets* `BDD_EXPECT_FAILED` on its own failure — it never *clears* a flag set
upstream. Failures are recorded per-example from this single flag at example end
(`bdd.rs` L703/724), so the eager mark stands and the example fails.

## Why the obvious fixes are unsafe

- **infix → PROVISIONAL** (like the hollow-call path) or **matcher clears
  FAILED on pass**: both rely on per-example flags, so in a multi-assertion
  example a *passing* later matcher would clear/override a *real* earlier
  `expect a == b` failure — masking it (FALSE-GREEN). `expect a == b` is the
  rewritten form of nearly every assertion, so this risk is broad. A passing
  self-test would hide it. Not worth it for one awkward-idiom spec.

A correct fix needs per-assertion (not per-example) result tracking in the BDD
runner — a non-trivial restructuring. Deferred.

## Workaround

Use the idiomatic matchers: `expect(a).to_not_equal(b)` (asserts inequality) or
`expect(a).to_equal(b)` — both already correct. Same family as
`harness_word_infix_expect_not_preprocessed_2026-06-29` (BDD eager-marking vs
trailing matcher).
