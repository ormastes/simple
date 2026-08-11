# Red-team audit — Modern SSpec typed-evidence contract (Wave 0 / lane E1)

Date: 2026-08-08
Target commit: `a19a939033cb5bea1e8dca229d455c524da9a669`
Targets:
- `src/lib/common/spec/evidence/model.spl`
- `src/lib/common/spec/evidence/evidence_comparator.spl`
- `test/01_unit/lib/common/spec/evidence/typed_evidence_oracle_spec.spl`

Method: adversarial probes importing the real modules, executed with
`SIMPLE_TIMEOUT_SECONDS=900 bin/simple run <probe>`. Probes:
`/tmp/claude-1000/-home-ormastes-dev-pub-simple/redteam_probe.spl` and
`redteam_probe2.spl`. **Everything below was EXECUTED**; nothing is reasoned-only
unless explicitly marked UNVERIFIED.

Binary caveat: `bin/simple` currently resolves to the Rust bootstrap seed (it
prints the seed banner). The findings are pure comparator logic with no engine-
sensitive constructs, but a re-run on the self-hosted binary is worth doing.

---

## F1 — BLOCKER: a bind-only oracle is vacuous but green

`check_bind` sets `mode = semantic` + `bind_name`, and `evaluate_check` returns
`EvidenceStatus.passed` **unconditionally** (comparator L255-256) the moment the
selector resolves. It then increments `positives` (L317), so the vacuity gate at
L336 (`positives == 0 and failures == 0`) is satisfied. An oracle consisting of
nothing but binds asserts **no value at all** yet reports PASS.

Observed:
```
A1 bind-only(closed) => PASS | 2 check(s) passed
A2 bind-only(open)   => PASS | 1 check(s) passed
D1 ignore+bind       => PASS | 1 check(s) passed
N6 bind empty value  => PASS | 1 check(s) passed
```
`D1` is the worst shape: one ignore (with a reason) plus one bind passes a
closed oracle over evidence where *nothing* was compared. `N6` shows a bind over
an **empty** value is also a "positive".

Smallest fix: a bind is a capture, not an assertion. Exclude `bind_name != ""`
checks from the `positives` counter, and add a vacuity gate requiring at least
one check that is neither `ignore` nor a pure bind. Optionally require every
`bind_name` to be consumed by a matching `check_same_as` in the same spec —
an uncorrelated bind is dead weight.

## F2 — BLOCKER: `numeric_tolerance` on non-numeric values passes

`.to_i64()` on garbage yields `0`, so two unrelated non-numeric strings both
become `0` and the tolerance test `abs(0-0) <= 0` succeeds (comparator
L248-250). No parse validation exists on either side.

Observed:
```
H1 numeric garbage => PASS | 1 check(s) passed
```
(expected `"elephant"`, actual `"banana"`, tolerance 0 — PASS.)

Smallest fix: validate both `check.expected` and `actual` as fully-numeric text
before comparing; a non-numeric operand must return `EvidenceStatus.failed` with
detail "non-numeric value in numeric_tolerance check". This is the same class of
defect the module's own header warns about for parse failures.

## F3 — MAJOR: tolerance arithmetic overflows into a pass

`abs_i64(got - want)` is computed in wrapping i64. With `want = i64::MAX` and
`got = i64::MIN` the subtraction wraps to a small magnitude and clears the
tolerance.

Observed:
```
N4 overflow => PASS | 1 check(s) passed
```
(expected `9223372036854775807`, actual `-9223372036854775808`, tolerance 1.)

Smallest fix: compare without subtracting — `if got > want: got - want else:
want - got` still overflows, so instead range-check: fail when
`want > 0 and got < 0` (or vice-versa) and the magnitudes exceed the tolerance,
or perform the comparison against `tolerance` using an ordered pair test
(`got >= want - tol and got <= want + tol` with saturating bounds).

Related, **not** broken: a negative tolerance fails closed (`N2 => FAIL`), and a
tolerance > 0 with no reason is correctly rejected by `ignores_have_reasons`
(`H2 => FAIL`). An absurdly large tolerance passes (`N3 => PASS`) but that is a
declared, reasoned choice, not a defect.

## F4 — MAJOR: `evidence_manifest_is_complete` accepts obviously fake hashes

The check is emptiness-only (model L511-520). A one-character `spec_sha256` and
an `artifact_sha256` of `"not-a-hash"` are accepted.

Observed:
```
M1 fake-hash manifest complete -> true
```
The module's own comment says the hashes are what make a manual "falsifiable" —
a manifest that accepts `"z"` as a sha256 does not deliver that. It should:
the whole point of the receipt is that a reader can recompute it.

Smallest fix: require both hash fields to be exactly 64 characters and all
lowercase-hex. `pattern_matches("hex:64", h)` already exists in the comparator
and does precisely this — move it (or a local copy) into the manifest check.

## F5 — MINOR: `check_exact("", "")` passes when an empty-path node exists

An empty selector path is not rejected at construction, and an evidence node with
an empty path and empty value satisfies it as a genuine positive.

Observed:
```
N5 empty path empty expect => PASS | 1 check(s) passed
```
Requires a degenerate producer to emit an empty-path node, so severity is minor,
but the "positive" is content-free. Smallest fix: reject an empty
`selector.path` at check-construction time (or fail the check in
`evaluate_check`) for every kind whose path is the whole selector.

## F6 — MINOR: `cardinality = 0` yields a content-free positive

A check with `cardinality = 0` and `expected = ""` passes when the path is absent
— `actual` defaults to `""` (L225) and the exact branch compares `"" == ""`.
It counts as a positive, so an oracle of only absence-checks reports PASS.

Observed:
```
F1 cardinality0 only => PASS | 1 check(s) passed
```
This is arguably a legitimate "field must be absent" assertion, which is why it
is only minor — but it is currently *implicit*, undocumented, and reachable only
by hand-mutating a defaults record. Encouragingly, it fails closed in the
opposite direction: a cardinality-0 check over a path that IS present fails
(`N7 => FAIL`). Smallest fix: give absence a named constructor
(`check_absent(path)`) with an explicit result detail, and decide deliberately
whether it counts toward `positives`.

## F7 — MINOR: duplicate bind names silently shadow

`binding_value` returns the first match, and `bindings.push` never rejects a
duplicate name, so a second `check_bind` with an existing name is silently
ignored and a later `check_same_as` correlates against the first capture.

Observed:
```
K1 dup bind names => PASS | 3 check(s) passed
```
(`a=AAA` and `b=BBB` both bound to `"id"`; `check_same_as("c","id")` matched
`AAA` — the reader cannot tell which binding was used.)

Smallest fix: fail the spec at the vacuity-gate stage when two checks declare the
same `bind_name`.

---

## What I could NOT break — clean results

These were attacked and held, fail-closed as documented:

- **Optional-only oracle** — all-optional, all-absent yields `ignored` statuses,
  `positives == 0`, and the L336 gate fires: `C1 => FAIL, no positive check
  resolved against the evidence`. The gate works.
- **Empty `expected_items`** in multiset over empty evidence — `E1 => FAIL`
  (cardinality `-1` requires ≥1 node). Ordered/multiset cannot be satisfied
  vacuously.
- **Ordering dependence** — `check_same_as` placed before its `check_bind`
  correctly fails with "correlation binding was never captured"
  (`J1 => FAIL`). Bindings are strictly left-to-right, which is the safe
  direction.
- **Pattern classes** — every garbage form was rejected: `hex:abc` (non-numeric
  count, `.to_i64()` → 0 → length mismatch), `hex:0`, `hex:-1`, and non-ASCII
  input (`alnum:*` on `"café"`, `digit:1` on `"¹"`) all returned `false`. The
  anchored-class design holds; there is no substring escape.
- **Closed-mode coverage** — I could not hide an undeclared field behind a
  declared path. Path matching is exact equality, and an extra node at a
  declared path trips the cardinality check instead. `N1` (a secret field
  shielded by `check_ignore("debug", "volatile")`) passes, but that is the
  *designed* semantics of a reasoned ignore, not a coverage hole.
- **Parse-error evidence** — first-class failed state, cannot be mistaken for an
  empty node set.

## Verdict

**The Wave-0 contract is structurally sound but NOT yet safe to build E2-E7 on
unmodified.** The architecture is right — fail-closed gates, anchored patterns,
cardinality, parse-error-as-state and the `positives == 0` backstop all held
under attack, and the closed-mode and pattern layers resisted every escape I
constructed. The defects are localized to three evaluator leaves, not to the
model.

However **F1 and F2 are blockers** and must land before downstream lanes adopt
the comparator, because both produce a **PASS that a manual reader would read as
verified evidence**: an oracle of binds asserts nothing, and a numeric-tolerance
check silently accepts arbitrary non-numeric text. Both are a handful of lines in
`evaluate_check`. F3 and F4 (major) should land in the same change — F4 in
particular is a two-line reuse of the existing `pattern_matches("hex:64", …)`.

Recommendation: gate E2-E7 adoption on F1-F4, and add each probe above to
`typed_evidence_oracle_spec.spl` as a red-then-green regression case so the
escapes cannot silently return.
