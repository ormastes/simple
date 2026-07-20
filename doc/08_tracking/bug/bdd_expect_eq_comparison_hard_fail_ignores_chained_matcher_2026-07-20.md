# SSpec `expect(a == b)`/`expect(a != b)` hard-fails before a chained matcher runs

- **ID:** bdd_expect_eq_comparison_hard_fail_ignores_chained_matcher_2026-07-20
- **Status:** FIXED (worktree `/tmp/wt_sspeceval`, not yet landed — a review/land
  lane owns pushing to origin)
- **Severity:** high-blast-radius false-RED in the SSpec interpreter evaluator
  (`simple test`) — NOT a value-marshaling / empty-value bug
- **Component:** `src/compiler_rust/compiler/src/interpreter_call/bdd.rs`,
  `eval_bdd_builtin`, `"expect"` case, `Expr::Binary { Eq | NotEq }` arm

## Origin of this investigation

Assigned to verify a hypothesis that the SSpec test evaluator (`simple test`)
silently returns EMPTY values from imported functions that work correctly
under `simple run` — using
`test/01_unit/lib/common/gpu/font_atlas_composite_identity_spec.spl` and
`test/01_unit/lib/common/text_layout/font_identity_free_function_spec.spl` as
motivating cases, plus a same-session sibling lane's independent report of a
C-extern array argument (`rt_core_as_array`) arriving empty under `test` but
not `run`.

**That hypothesis is disproven for the font-atlas case.** The 141-char
identity key computed by `font_atlas_composite_cache_identity` (imported
across a module boundary) is correct and non-empty on both sides of every
comparison in both failing examples — verified by reading the raw failure
text emitted before the fix (see Evidence). The apparent "empty" in one
failure message is the *correct*, by-design fail-closed `""` returned by
`_identity("", ...)`, which a separate, correctly-passing `.to_equal("")`
matcher legitimately matched. The real defect is upstream of any value
computation: a pass/fail bookkeeping bug in the interpreter's built-in
`expect(...)` intrinsic itself.

The sibling lane's `rt_core_as_array` finding (array argument to a C extern
arriving NULL under `test`, not `run`) is a **different, real defect** not
touched by this fix — see "Relation to the array-marshaling report" below.

## Symptom

`expect(a == b).to_be(false)` (or `.to_equal(false)`, or the `!=` /
`.to_be(true)` mirror) false-reddens the enclosing `it` example even when
`a != b` and the chained matcher legitimately passes. `expect(a == b)` with
no chained matcher continues to correctly fail on a mismatch (that path is
unaffected).

## Reproduction

```
describe "font atlas composite cache identity":
    it "keeps the six native font targets distinct":
        var keys: [text] = []
        for backend in ["cuda", "metal", "opencl", "rocm", "vulkan2d", "vulkan3d"]:
            val key = _identity("material", backend, "device", "artifact", "dependency")
            for prior in keys:
                expect(key == prior).to_be(false)   # key != prior, so this SHOULD pass
            keys.push(key)
```

Pre-fix, `bin/simple test test/01_unit/lib/common/gpu/font_atlas_composite_identity_spec.spl`:

```
✗ is stable, target-aware, collision-safe, and fail-closed
    expected call result to be truthy, got
✗ keeps the six native font targets distinct
    expected font-atlas-composite-cache-v1|...backend=8:vulkan3d|... to equal
    font-atlas-composite-cache-v1|...backend=8:vulkan2d|...
2 examples, 2 failures
```

Both displayed messages are *stale* — `BDD_FAILURE_MSG` is a single global
slot overwritten by every assertion, hard or provisional; the message shown
is whichever assertion wrote last, not necessarily the one that actually
tripped `BDD_EXPECT_FAILED`. In example 1 the real trip was the very first
`expect(base == _identity("material-2",...)).to_be(false)` (base != that
variant, so the equality is false — exactly what the test wants); the
displayed message came from a much later, correctly-passing
`expect(_identity("",...)).to_equal("")` assertion whose call result really
is `""` by design (fail-closed on an empty parameter).

## Root cause

`eval_bdd_builtin`'s `"expect"` case special-cases the first argument
expression to distinguish two call shapes:
1. `expect(value).to_matcher(...)` — a real chained matcher follows, and is
   authoritative (`interpreter_method/mod.rs` sets/clears
   `BDD_EXPECT_FAILED` itself).
2. `expect a == b` (SPipe-legacy infix form, rewritten to `expect(a == b)`
   with **no** chain) — this handler is the *only* place that can catch a
   mismatch, since nothing downstream will check the returned bool.

To tell them apart without a syntactic look-ahead, comparison-form subjects
mark failure **provisionally** (`BDD_EXPECT_PROVISIONAL`, not
`BDD_EXPECT_FAILED`): if a real matcher chain follows, `matcher_ran` gets
set and the provisional mark is disregarded at end-of-example
(`failed = hard_failed || (provisional && !matcher_ran)`); if no matcher
chain follows, the provisional mark stands and the example still fails.

This provisional/hard split was already correctly implemented for the
**ordered comparison** operators (`<`, `<=`, `>`, `>=`) — see the code
comment there explicitly describing this exact bug (*"Hard-failing here
false-reddened every `expect(a < b).to_equal(false)` even though the
assertion passes"*) as the reason it uses `BDD_EXPECT_PROVISIONAL`.

**The `Eq`/`NotEq` arm was never given the same fix.** It still set the hard
`BDD_EXPECT_FAILED` flag directly on any `==`/`!=` mismatch:

```rust
// src/compiler_rust/compiler/src/interpreter_call/bdd.rs (pre-fix, ~line 903)
if !matched {
    BDD_EXPECT_FAILED.with(|cell| *cell.borrow_mut() = true);   // HARD, never cleared
    ...
}
```

Per `interpreter_method/mod.rs`, every matcher (`to_equal`, `to_be`, ...)
sets `BDD_EXPECT_FAILED = true` on mismatch but **never** sets it back to
`false` on a match — a passing matcher cannot undo an already-hard failure.
So `expect(a == b).to_be(false)` with `a != b`:
1. `is_cmp_form` (`Expr::Binary{Eq}`) evaluates `a == b` → `false` →
   `matched = false` → `!matched` → **hard** `BDD_EXPECT_FAILED = true`.
2. The chained `.to_be(false)` matcher then runs, correctly sees
   `Bool(false) == false`, and passes — but a passing matcher never clears a
   hard failure.
3. At example end, `hard_failed = true` regardless of the passing matcher →
   the example is reported as failed.

## Fix

Mirror the ordered-comparison arm: mark `Eq`/`NotEq` mismatches
**provisional** instead of hard.

```rust
// src/compiler_rust/compiler/src/interpreter_call/bdd.rs
if !matched {
    BDD_EXPECT_PROVISIONAL.with(|cell| *cell.borrow_mut() = true);
    BDD_FAILURE_MSG.with(|cell| { ... "expected {left} to {op_word} {right}" ... });
}
return Ok(Some(Value::Bool(matched)));
```

A bare `expect a == b` (no chain) still correctly fails: `matcher_ran` stays
false, so `provisional && !matcher_ran` is true at example end. A chained
`.to_be(false)`/`.to_equal(false)`/`.to_be(true)` now correctly overrides the
provisional mark with its own (accurate) verdict.

## Verification

Built the patched Rust seed (`cargo build --manifest-path
src/compiler_rust/Cargo.toml --profile bootstrap -p simple-driver`, ~3m40s)
and re-ran under `bin/simple test` (the seed is what `simple test`'s
interpreter path actually runs today):

| Spec | Before | After |
|---|---|---|
| `font_atlas_composite_identity_spec.spl` | Passed: 0, Failed: 2 | **Passed: 2, Failed: 0** |
| New regression spec (below), 5 chained-matcher cases | n/a (bug pre-dates spec) | **Passed: 5** |
| New regression spec, 1 bare-form deliberate-fail case | n/a | **Failed: 1 (correctly, unchanged)** |

Sampled for regressions (all identical before/after fix — no behavior change
outside the Eq/NotEq-with-chained-matcher case):
- `test/01_unit/compiler/bdd_text_eq_runtime_spec.spl` — 2 pass, 1
  documented deliberate-fail RED (unchanged)
- `test/01_unit/compiler/bdd_truthy_runtime_spec.spl` — 4 pass (unchanged;
  its "deliberate-fail RED" case is a bare integer literal, a different code
  path (`is_call_expr`), not touched by this fix — pre-existing on both the
  original and patched binary)
- `test/01_unit/lib/nogc_sync_mut/spec_bool_expect_spec.spl` — 2 pass, 1 fail
  (`expect_not(false)`) — identical on original and patched binary; a
  separate, pre-existing, unrelated bug in `expect_not`, out of scope here

## Regression spec

Added `test/01_unit/compiler/bdd_eq_chained_matcher_provisional_spec.spl`:
five chained-matcher cases (`==`/`!=` crossed with `to_be(true|false)` /
`to_equal(false)`) that must pass, plus one bare `expect 1 == 2` with no
chain that must keep failing — the discriminating pair that would have
caught this exact regression (a spec asserting only "imported function
returns non-empty" would NOT have caught it, since no value was ever lost).

## Unrelated finding surfaced along the way

`test/01_unit/lib/common/text_layout/font_identity_free_function_spec.spl`
fails identically before and after this fix with `semantic: class
'FontRenderBatch' has no field named 'atlas_owner_generation'` — a genuine,
pre-existing struct/spec drift unrelated to the BDD bug or to value
marshaling. Not fixed here (out of scope); worth a separate bug entry if one
does not already exist.

## Relation to the array-marshaling report (`rt_core_as_array` / `rt_bytes_to_text`)

A sibling lane reported a C extern receiving a NULL/empty `[u8]` argument
under `test` but not `run`, and hypothesized a shared root with this
investigation ("values crossing a boundary lose their payload" in both
cases). Based on the evidence above, **these are different bugs**:

- This bug is a pure interpreter-side pass/fail *bookkeeping* defect inside
  `eval_bdd_builtin`'s `expect` handler. No value is lost, corrupted, or
  fails to cross any boundary — `left_val`/`right_val` are correctly
  evaluated and correctly compared in every case observed; the only thing
  wrong is which global flag the *comparison result* sets.
- The reported array-marshaling defect is a value actually arriving
  NULL/empty at a C extern call boundary — a genuine payload-loss bug this
  fix does not touch, and this investigation did not need to (or attempt to)
  explain or fix it.

Both bugs share only the surface symptom "something looks empty under
`test` but not `run`" and the fact that both live somewhere in the
interpreter path `simple test` uses — they do not share a mechanism, and
fixing one does not fix the other. Treat as two separate bugs/fixes.

## Blast radius

This bug is a **false-RED**, not a silent false-green: every
`expect(a == b).to_be(false)` (or the `!=`/`true` mirrors) in the suite was
*already visibly failing* wherever it appeared, so it cannot have hidden a
real defect behind a passing test — the opposite of the feared "green tests
may be meaningless" scenario. Detection for existing occurrences: grep specs
for chained matchers over a comparison-form subject, e.g.
`grep -rn 'expect(.*[=!]=.*)\.\(to_be\|to_equal\)' test/` — every hit was a
visibly failing (not silently passing) example prior to this fix, so the
practical remediation is simply "re-run the suite after this fix lands and
watch previously-red examples of this exact shape turn green."
