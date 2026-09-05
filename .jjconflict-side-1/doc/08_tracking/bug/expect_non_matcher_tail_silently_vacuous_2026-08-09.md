# `expect(X).<non-matcher>()` and `expect(X) <arith>` are SILENTLY VACUOUS

**ID:** expect_non_matcher_tail_silently_vacuous_2026-08-09
**Status:** FIXED 2026-08-09 (see RESOLUTION at end)
**Severity:** Medium (bounded — 41 sites, enumerated below)
**Found by:** stream F6, by EXECUTION (6 probe specs, verdict lines quoted verbatim)
**Supersedes the diagnosis in:** stream F2's `expect (result - 5.0).abs() < 0.001` report

---

## Summary

F2 reported that `expect (result - 5.0).abs() < 0.001` degrades to a bare
truthiness assertion, and attributed it to **the SPACE after `expect`**.

**The space is NOT the cause.** `expect(x).abs() < 0.001` with NO space is
equally vacuous (probe 3, NOSPACE1/NOSPACE2 both PASS on deliberately-false
claims). The repo-wide `expect (` count of 373/383 is therefore **not** the
blast radius and should not be used as one.

**`expect (x).to_equal(y)` — space then a matcher — is CORRECT and NOT
vacuous.** This was the critical unknown; it is settled by execution below.
That bounds the damage enormously.

## The actual rule (all four arms executed)

Given a statement `expect(X)<TAIL>`:

| TAIL | behaviour | vacuous? |
|---|---|---|
| *(empty)* | truthiness assertion on `X` (bool overload) | no |
| `.M(...)` where `M` is a **matcher** (`to_equal`, `to_contain`, `to_not_equal`, `.to(eq())`, …) | matcher runs, replaces the provisional result via `_begin_matcher()` | **no** |
| `.M(...)` where `M` is **not a matcher but exists on `X`'s own type** (`.abs()`, `.contains()`, `.fdiv()`) | `ExpectHelper` auto-unwraps to `X`; `M` runs on `X`; the whole tail is an **expression statement whose value is dropped**. Only `X`'s truthiness was asserted — and for a non-bool-coercible `X` (e.g. `text`) **nothing at all** was asserted | **YES** |
| `.M(...)` where `M` exists **nowhere** (`.not.`, `.not_to_be_nil`, `.to_be_i64`) | hard `semantic:` error | no (fails **closed**) |
| `== Y` / `!= Y` alone | folds into the `expect` argument | no |
| `+ 3 == Y`, `* 4 == Y`, `/ 2 == Y`, `% 5 == Y` (**arithmetic** first) | binds as `(expect(X) <op> …)`, dropped | **YES** |

### Why (source)

`src/lib/nogc_sync_mut/spec.spl:643-651`:

```
pub fn expect(value: bool) -> ExpectHelper:      # asserts immediately
    if not value:
        fail_assertion("Expected true, got false")
    ExpectHelper(value: value, negated: false, implicit_error: not value)

pub fn expect(value) -> ExpectHelper:            # NON-bool: asserts NOTHING
    ExpectHelper(value: value, negated: false, implicit_error: false)
```

A matcher calls `_begin_matcher()` (`spec.spl:668-673`), which pops the
provisional error and substitutes its own comparison. A **non-matcher** tail
never calls it — so the provisional result stands, and for the generic
(non-bool) overload there is no provisional result at all.

Note there are **two** matcher implementations: the `.spl` `ExpectHelper` and a
set of Rust interpreter intrinsics (`to_not_equal`, `to_not_contain`,
`to_not_be_nil`, `.to(eq())`, `.not_to()` — visible from their Rust-shaped
failure text `expected Int(1) to match Matcher(Exact(Int(2)))`). Any census that
uses only the `.spl` list will produce ~1,300 false positives.

---

## Executed evidence

All probes under `test/01_unit/spec_harness/`. Binary: seed
`bin/release/x86_64-unknown-linux-gnu/simple`. Interpreter lane.

### Probe 2 — does space+matcher degrade? (the critical unknown)

```
SPEC FILE VERDICT: test/01_unit/spec_harness/expect_space_paren_discriminate_spec.spl declared>=9 executed=9 passed=7 failed=2 dropped=0
```

| case | expect | actual | vacuous |
|---|---|---|---|
| `expect (true).to_equal(true)` | PASS | **PASS** | no |
| `expect (1 + 1).to_equal(2)` | PASS | **PASS** | no |
| `expect ("abcdef").to_contain("cde")` | PASS | **PASS** | no |
| `expect (0.5).to_be_less_than(1.0)` | PASS | **PASS** | no |
| `expect (false).to_equal(true)` (probe 1) | FAIL | **FAIL** | no |
| `expect (1 + 1).to_equal(99)` (probe 1) | FAIL | **FAIL** | no |
| `expect (0 + 5).abs() > 999` | FAIL | **PASS** | **YES** |
| `expect (10.0 / 2.0 - 1.0).abs() < 0.001` | FAIL | **PASS** | **YES** |
| `expect (7) == 8` | FAIL | **FAIL** | no |

The true-case column is what makes this conclusive: under the hypothesised
vacuous parse `expect((x).to_equal(y))` the matcher's nil return would make the
TRUE cases fail too. They pass. **The matcher genuinely runs.**

### Probe 3 — is the space the cause? NO

```
SPEC FILE VERDICT: test/01_unit/spec_harness/expect_space_paren_mechanism_spec.spl declared>=6 executed=6 passed=4 failed=2 dropped=0
```

| case | expect | actual |
|---|---|---|
| `expect(0 + 5).abs() > 999` **no space** | FAIL | **PASS** — space irrelevant |
| `expect(10.0 / 2.0 - 1.0).abs() < 0.001` **no space** | FAIL | **PASS** — space irrelevant |
| `expect (0 + 5).abs() > 999` space | FAIL | **PASS** |
| `expect(0).abs() > 999` falsy prefix | FAIL | FAIL |
| `expect(0 + 5).to_equal_XYZ(999)` | FAIL | FAIL — `semantic: method to_equal_XYZ not found on type i64 (receiver value: 5)` |

The receiver in that error is **`i64` value `5`**, not an `ExpectHelper` — this
is the direct proof of the auto-unwrap mechanism.

### Probe 5 / 6 — family sweep

```
SPEC FILE VERDICT: test/01_unit/spec_harness/expect_hazard_families_spec.spl declared>=12 executed=12 passed=2 failed=10 dropped=0
SPEC FILE VERDICT: test/01_unit/spec_harness/expect_hazard_final_spec.spl declared>=6 executed=6 passed=5 failed=1 dropped=0
```

| family | false case | verdict |
|---|---|---|
| `.contains(...)` on text | `expect ("abcdef").contains("zzz")` | **PASS → VACUOUS** (and the true case passes too — text takes the generic overload, so *nothing* is asserted) |
| `.fdiv(n) == wrong` | `expect (-7).fdiv(2) == 99999` | **PASS → VACUOUS** |
| arithmetic tail | `expect ((-5)) + 3 == 99999` | **PASS → VACUOUS** |
| `.not.to_contain(...)` | | FAIL — `semantic: undefined field: unknown property or method 'not' on String` (fails closed) |
| `.not_to_be_nil()` | | FAIL — `semantic: method not_to_be_nil not found on type nil` (fails closed) |
| `.to_be_i64()` | | FAIL — `semantic: method to_be_i64 not found on type str` (fails closed) |
| `expect(2 + 2) == 5` | | FAIL (correct) |

---

## Blast radius — 41 sites, enumerated

Not 373. Full list: `scratchpad/vacuous_sites.tsv` (regenerable with the census
in this doc's history). By file:

| count | file | shape |
|---|---|---|
| 12 | `test/03_system/feature/usage/arithmetic_spec.spl` | arithmetic tail |
| 12 | `test/feature/usage/arithmetic_spec.spl` (duplicate tree) | arithmetic tail |
| 4 | `test/01_unit/lib/security/.spipe_wrapped_entry_remote_security_quorum_spec.spl` | `.contains()` |
| 2 | `test/03_system/feature/usage/llvm_backend_spec.spl` (:89, :168) | `.abs() < 0.001` — **F2's file** |
| 2 | `test/03_system/gui/editor_gui_sdl_spec.spl` (:14, :18) | `.contains()` |
| 2 | `test/system/editor_gui_sdl_spec.spl` (:14, :18) | `.contains()` |
| 1 | `test/03_system/feature/usage/operators_advanced_spec.spl:296` | `.fdiv()` |
| 1 | `test/feature/usage/operators_advanced_spec.spl:296` | `.fdiv()` |
| 1 | `test/03_system/feature/usage/parser_operators_spec.spl:288` | arithmetic tail |
| 1 | `test/feature/usage/parser_operators_spec.spl:288` | arithmetic tail |
| 1 | `test/shared/core/arithmetic_spec.spl:38` | arithmetic tail |
| 1 | `test/01_unit/lib/std/json_spec.spl:53` | `.abs() < 0.001 to_be_true` (also hard-errors on `to_be_true`) |
| 1 | `test/unit/lib/std/json_spec.spl:53` | same |

The irony worth flagging: **the arithmetic specs are the ones that cannot check
arithmetic.** 27 of the 41 are in `arithmetic_spec.spl` / `parser_operators_spec.spl`
/ `operators_advanced_spec.spl`.

### Separately: ~46 sites that hard-error (loud, not silent)

`.not.to_equal(...)` / `.not.to_contain(...)` (25), `.not_to_be_nil()` /
`.not_to_contain()` / `.not_to_equal()` (21), `.to_be_i64()` (2), `.value()` (8).
These fail closed with `semantic:` errors, so those examples are RED today.
Not this bug, but they imply those spec files are not green. Worth a separate
triage — the correct spellings are `to_not_*`, not `not_to_*`.

---

### Census undercount — READ BEFORE TRUSTING THE 41

The 41 is a **floor, not a total.** When the fix below was trialled on
`editor_gui_sdl_spec.spl`, the `expect (src).contains(...)` → `expect(src).to_contain(...)`
rewrite touched **~50 lines in that one file**, though the census had reported
only 2 sites in it. The paren-balancing line-joiner swallows following lines in
files where `expect` statements sit in tight `it` blocks, so most sites in such
a file are attributed to the first one. The true repo-wide count is higher than
41 — likely a few hundred — and **must be re-derived with a real parser, not
this regex, before any decision to sweep.** Do not quote 41 as the total.

## PROVEN in a production spec (sabotage transcript)

`test/03_system/gui/editor_gui_sdl_spec.spl`, unmodified, all green:

```
SPEC FILE VERDICT: ... declared>=19 executed=19 passed=19 failed=0 dropped=0
```

Sabotage — replace a real needle with one that cannot occur, leaving `.contains()`:

```
expect (src).contains("gui_sdl_bridge")  ->  expect (src).contains("ZZZ_NEVER_PRESENT_ZZZ")
SPEC FILE VERDICT: ... declared>=19 executed=19 passed=19 failed=0 dropped=0
```

**Still 19/19 green.** The assertion cannot fail. Now apply the fix, keeping the
sabotaged needle:

```
expect(src).to_contain("ZZZ_NEVER_PRESENT_ZZZ")
SPEC FILE VERDICT: ... declared>=19 executed=19 passed=17 failed=2 dropped=0
```

The fix restores fail-on-broken-code. Needle restored, fix retained:

```
SPEC FILE VERDICT: ... declared>=19 executed=19 passed=18 failed=1 dropped=0
```

### The fix EXPOSED A REAL, PREVIOUSLY-HIDDEN DEFECT

That remaining failure is not an artefact — it is a genuine product regression
the vacuous assertion had been masking:

- `test/03_system/gui/editor_gui_sdl_spec.spl:118` *"main exposes --gui-sdl mode"*
- asserts `src/app/editor/main.spl` contains `"--gui-sdl"` and
  `gui_shell_run_sdl(session)`
- it does not. `main.spl` is now a *"Startup-light CLI surface for source-mode
  help and readiness probes"* — the `--gui-sdl` entrypoint is gone.

The same failure appears in the `test/system/` mirror (17/18). **This is the
concrete proof that the bug hides real breakage, not just theoretical risk.**

**The spec edits were deliberately NOT landed.** A ~50-line rewrite across two
files is a sweep, and it turns `main` red on a pre-existing product defect that
is not this stream's to triage. Enumerated, proven, and left for the owner —
per the standing "enumerate, do not sweep" rule.

## Recommended fix

**Do not mass-rewrite the specs.** The durable fix is in the DSL, not the sites:

1. Make `ExpectHelper` **not auto-unwrap**. An unknown method on an
   `ExpectHelper` should be a hard error (like `to_equal_XYZ` already is)
   instead of silently forwarding to the wrapped value. That converts all 14
   non-matcher-method sites from silent-pass to loud-fail.
2. Make the **generic (non-bool) `expect(value)` overload** record a pending
   assertion that fails the example if no matcher ever consumed it. Today it is
   a total no-op — `expect("some text")` asserts nothing whatsoever, which is a
   fail-open primitive independent of this bug.

### A lint WOULD catch this cheaply

The census in this doc is ~40 lines of paren-balanced scanning: find statements
matching `^expect\s*\(`, balance to the argument's closing paren, and flag when
the tail (a) starts with `.` and the method is not in the matcher set, or
(b) starts with an arithmetic operator. Both matcher sets must be unioned
(`spec.spl` + the Rust intrinsics) or it produces ~1,300 false positives.
This is small enough to be worth doing and is recommended.

## Uncertainties stated plainly

- Everything here is the **interpreter** lane (`bin/simple test`). Not
  established for the JIT/native lanes; spec bodies cannot reach them anyway.
- The exact parser production that makes `+ 3 == Y` bind differently from
  `== Y` was **not** identified — the split is reported as executed behaviour,
  not as a cited grammar rule.
- The `.tsv` enumeration is regex+paren-balance based. It matches only
  single-statement forms starting at column-leading `expect(`; an `expect` in
  the middle of a compound line would be missed.
- `test/feature/**`, `test/unit/**`, `test/system/**`, `test/shared/**` appear
  to be a duplicate/legacy mirror of the numbered trees; ~13 of the 41 are that
  mirror, so the distinct-source count is closer to **28**.

---

# RESOLUTION 2026-08-09 (stream G1) — FIXED at the DSL level

**Status: FIXED.** Fixed in the DSL, not by sweeping the 41 call sites. The
sites above are now RED and are real defects; they must be fixed on their
merits, not by weakening the gate.

## Premise correction: `spec.spl` is DEAD CODE on the shipping test path

The "Why (source)" section above cites `src/lib/nogc_sync_mut/spec.spl:643-651`.
That file is **never reached** by `bin/simple test`. Proven by sabotage:
inserting an unconditional `fail_assertion` into the generic
`pub fn expect(value)` overload left a 4-example probe at
`SPEC FILE VERDICT ... executed=4 passed=4 failed=0`.

The live implementation is the Rust seed BDD interpreter:
`src/compiler_rust/compiler/src/interpreter_call/bdd.rs` (the `"expect"` arm)
plus the matcher arm in `src/compiler_rust/compiler/src/interpreter_method/mod.rs`.
Any future fix aimed only at `spec.spl` is a no-op.

## The fix

A counter-based vacuity gate reusing the existing provisional/matcher plumbing:

- `BDD_EXPECT_NEEDS_MATCHER` — incremented for every `expect(<non-bool subject>)`.
- `BDD_MATCHER_COUNT` — incremented wherever `BDD_MATCHER_RAN` is already set.
- At example end, `needs > matchers` fails the example with a `vacuous expect:`
  message naming the unconsumed subject.

Counters rather than a single flag, so a vacuous `expect(c).len()` is still
caught when a sibling `expect(a).to_equal(b)` in the same example did chain a
matcher.

Bool subjects are deliberately exempt: bare `expect(<bool>)` remains a real
truthiness assertion (row 1 of the table above, and the 2026-08-02
bare-assert-vacuity fix). `expect(a == b)` / `expect(a < b)` return through the
earlier comparison arms and are unaffected (rows 5).

Rows 3 and 6 — the two **YES** rows — are both non-bool subjects and are both
now caught. Note this did **not** require stopping the `ExpectHelper`
auto-unwrap: `expect(...)` still returns the subject value, so chaining
semantics are untouched; the gate catches the vacuity independently. That is
strictly less invasive than removing the unwrap.

`src/lib/nogc_sync_mut/spec.spl` was mirrored for the future pure-Simple path
(generic `expect` now records a provisional failure that the first matcher pops
via `_begin_matcher()`, exactly like the bool overload).

## Spec

`test/03_system/check/expect_vacuity_gate_spec.spl` — 5 examples covering both
directions. The negative half generates fixtures and runs them through a child
compiler, asserting they go red; the positive half asserts every correct usage
still passes (chained matchers, matchers on falsy non-bool subjects, bare
`expect(<bool>)`).

```
SPEC FILE VERDICT: test/03_system/check/expect_vacuity_gate_spec.spl declared>=5 executed=5 passed=5 failed=0 dropped=0
```

## Newly RED — real defects, left RED

```
BEFORE: SPEC FILE VERDICT: test/03_system/gui/editor_gui_sdl_spec.spl declared>=19 executed=19 passed=19 failed=0 dropped=0
AFTER : SPEC FILE VERDICT: test/03_system/gui/editor_gui_sdl_spec.spl declared>=19 executed=19 passed=0  failed=19 dropped=0
```

`test/03_system/gui/editor_gui_sdl_spec.spl` was 19/19 green on a needle that
cannot occur: `src/app/editor/main.spl` no longer has the `--gui-sdl`
entrypoint. **Unblock condition:** restore the `--gui-sdl` entrypoint in
`src/app/editor/main.spl`, or retarget the spec at whatever replaced it. Do NOT
soften the assertions. Its duplicate-tree twin `test/system/editor_gui_sdl_spec.spl`
has the same two sites and is expected to go red identically.

The other 39 enumerated sites above are expected to go red on the same
mechanism; each needs a real matcher chained (`.to_be_close_to(...)`,
`.to_contain(...)`, `.to_equal(...)`) rather than a dropped expression tail.

## Measured non-regression

`test/01_unit/spec` (9 files, 141 examples): `Results: 141 total, 136 passed,
5 failed` — **zero** new reds. The failures there (`dsl_spec.spl` 11/3,
`matchers_spec.spl` 0/1) are pre-existing and unrelated: an `import` vs `use`
error, an array out-of-bounds, and an arity mismatch. No `vacuous expect`
message appears in that run.

## Verification binary

`bin/simple` is a stale deployed seed (2026-08-09 04:50) predating this gate and
was **not** relinked. All evidence above was produced with a freshly built
`src/compiler_rust/target/bootstrap/simple`. The gate spec honours
`$SIMPLE_SPEC_BIN` for that reason and passes on the `bin/simple` default once a
redeploy happens.

## Incidental unblocks (NOT part of this fix, left uncommitted by G1)

The seed did not build at all in this working tree. Three pre-existing breaks
from other sessions' in-flight work had to be worked around locally:
`runtime/src/value/sffi/env_process.rs:1223` (`String` vs `&str`), and two
"source-list-absent" link failures (`rt_packed_span_v1_*`, `rt_counterpart_*`)
whose C files exist but were never registered in
`src/compiler_rust/runtime/build.rs`.
