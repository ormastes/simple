# COLL020: `simple lint` said "all files clean" on a shape `simple fix` rewrote as Certain

**Status:** FIXED 2026-09-19 — one admission rule (`collection_certain_fixes`)
for both paths; detector extended to the two-array shape.
**Severity:** High — a machine-applicable rewrite offered for a finding the
linter denied existed. An LLM (this rule family's stated audience) that runs
`simple lint` and believes it has no collection problem gets its file
rewritten by `simple fix` anyway.
**Affected files:** `src/compiler/35.semantics/lint/collection_patterns.spl`,
`src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl`,
`src/compiler/90.tools/fix/main.spl`
**Spec files:** `test/01_unit/compiler/lint/collection_two_array_dedup_spec.spl`
(mirrored byte-identically at `test/unit/compiler/lint/`),
`test/01_unit/compiler/lint/collection_frame_rules_spec.spl`
**Path:** `bug` track. Found by a Fable audit of the LLM-safe-collections
("dataframe way") feature.

## Symptom

Fixture (`coll020_two_array.spl`), the two-array dedup idiom — a `seen` guard
array and a separate `out` result array, which is the most common dedup shape
an LLM writes:

```
fn dedup2(xs: [i64]) -> [i64]:
    var seen: [i64] = []
    var out: [i64] = []
    for x in xs:
        if not seen.contains(x):
            seen.push(x)
            out.push(x)
    out
```

Measured on the deployed Rust seed (`bin/simple`, v1.0.0-beta.12; note the
seed does NOT carry the `lint --fix` flag patch, so the fix path was exercised
through `simple fix`, not `simple lint --fix`):

```
$ bin/simple lint .../coll020_two_array.spl
Lint passed: all files clean

$ bin/simple fix .../coll020_two_array.spl --dry-run
Dry run for .../coll020_two_array.spl:
  1 fix(es) applied
  [COLL020] track membership in `seen_set` Dict instead of `.contains` on `seen`
```

Reproduced twice in the audit. The applied rewrite was, as it happens,
correct — which is worse, not better: nothing about the arrangement made it
so, and there was no gate that would have stopped a wrong one.

## Cause

Two callers of one generator with two different admission rules.

- `simple lint` produced the COLL020 diagnostic from the AST detector
  (`check_collection_patterns`) and attached `collection_020_fix` only when
  that detector fired (`entry_and_fixes.spl`, the `warning.code == "COLL020"`
  arm).
- `simple fix` called `collection_020_fix` **directly** on the raw source
  text, with no AST gate at all (`fix/main.spl`, the
  `if source.contains(".contains(")` block).
- The detector (`is_manual_distinct_loop`) required the loop body to be
  EXACTLY one statement and the guard's receiver to be the only array pushed
  to, and its header comment explicitly disclaimed the two-array shape as
  "a different (two-array) shape this detector deliberately does not claim,
  since matching it reliably needs alias analysis this AST walker lacks".

The disclaimer was only ever true of the detector. `collection_020_fix` is
textual and never read it.

## Fix

One truth, in the detector's favour.

1. `is_manual_distinct_guard` (replacing `is_manual_distinct_loop`) recognises
   a guard `if not <seen>.contains(<x>):` whose then-branch is a run of
   `<array>.push(<x>)` statements — every one pushing the value the guard
   tested, at least one onto the guard's own receiver. No alias analysis was
   needed: the shape is defined by the VALUE, not by any claim about how the
   two arrays relate. Guards nested inside `if`/block wrappers count, and
   `while` bodies are scanned like `for` bodies (the textual generator already
   accepted a `while ` header).
2. `collection_certain_fixes` (`entry_and_fixes.spl`) is now the single door
   to the COLL002/COLL020 Certain fixes: detector first, then the generator's
   textual preconditions, fix only when both agree. `simple fix` calls it
   instead of the raw generators. Lint warning WITHOUT a fix stays normal
   (hint-only); a fix without a warning is now impossible.
3. `collection_020_fix` gained the call-argument aliasing check COLL002 has
   had since its a23 fixture. `grow(seen, x)` in the loop can mutate the array
   through the callee where `collection_range_mutates` cannot see it, leaving
   the hoisted Dict out of step — a real hole in a fix claiming Certain,
   independent of the disagreement above.

`collection_frame_rules_spec.spl`'s example asserting COLL020 "stays silent on
the two-array seen/result shape (documented scope limit)" is flipped, with the
reason recorded in the example body.

## Verification

```
$ bin/simple lint .../coll020_two_array.spl
.../coll020_two_array.spl:5:9: warning[COLL020]: manual dedup loop (.contains
guard + .push of the guarded value) is O(n^2); switch to distinct_by(xs, key)
or unique() (std.common.frame) — dataframe-able. ...
  fix: available [COLL020] (certain)
Found 0 error(s), 1 warning(s), 1 auto-fix(es) available

$ bin/simple fix .../coll020_two_array.spl --dry-run
  1 fix(es) applied
  [COLL020] track membership in `seen_set` Dict instead of `.contains` on `seen`
```

Specs: `collection_two_array_dedup_spec` 8/8 (including a battery invariant —
every id `collection_certain_fixes` offers must be a code `lint_cli_source`
reported, across 7 fixtures, with a non-vacuity check), `collection_frame_rules_spec`
21/21, `collection_easy_fix_spec` 10/10, `collection_fix_adversarial_spec`
19/19, `lint_fix_apply_spec` 3/3, `collection_patterns_lint_spec` 12/12.

## Known limit, stated rather than papered over

`collection_020_fix` on its own still accepts shapes the detector refuses
(e.g. an early `break` inside the guard). Those rewrites happen to be
equivalent, but they are no longer reachable from either CLI, because the
door gates them. `collection_two_array_dedup_spec`'s T3 example asserts BOTH
facts, so the day the generator changes, the spec says so.

## Pre-existing test-tree divergence stepped over (recorded per .claude/rules/vcs.md)

`sh scripts/check/check-test-tree-divergence-delta.shs 7c875a81067 HEAD`:

```
base verdict: check-test-tree-divergence: FAIL — 3922 diverged vs 965
  baselined (3066 new, 109 fixed-but-still-baselined); 32 mirror-only
  (31 unallowlisted, 0 stale-allowlist)
PASS — 3206 pre-existing offender(s), 0 introduced by this range
```

The red is identical at BASE and NEW; this range introduces nothing. The two
spec files this lane adds/edits under `test/01_unit/compiler/lint/` are
mirrored **byte-identically** to `test/unit/compiler/lint/` (verified with
`cmp`), so they are not offenders in either direction. Offender list as saved
by the helper: `/tmp/test_tree_divergence_preexisting.txt` (3206 entries, not
copied into the tree — it is BASE state, not a product of this change).

## Third surface checked: `src/app/cli/query_lint.spl` (LSP/MCP diagnostics)

Checked because the repo has form for exactly this (see the STUB003 "the live
emitter is the text reimplementation, not this AST checker" note in
`entry_and_fixes.spl`). It is **not** a third admission rule: it calls the same
`check_collection_patterns(decl_indices)` (`query_lint.spl`, the `--- C2:
COLL001-008` block), so the detector is still the single source of the
findings, and it deliberately never raises a COLL to LSP-error severity
("Query collection diagnostics are still source-pattern facts").

It did, however, have its OWN position recovery — `_query_callable_line(
locations, w.item_name)` with the column hardcoded to `1` — so every COLL
diagnostic an editor or MCP client saw pointed at the enclosing function
header. Changed to prefer `w.line`/`w.column` with that as the fallback, the
same rule the CLI path uses.

**That change is UNVERIFIED BY EXECUTION, and here is why.** `query_lint.spl`
does not compile on the deployed seed, before this lane and independently of
it:

```
$ bin/simple test test/01_unit/compiler/lint/collection_two_array_dedup_spec.spl
error: compile failed: parse: in .../src/app/cli/query_lint.spl:
  Unexpected token: expected identifier, found Assign
```

Reproduced against the **pristine** `HEAD` copy of the file (`git checkout --`
first), so it is pre-existing and not introduced here. Consequences, stated
rather than glossed:

- No spec in this lane can import anything from that module, so the intended
  example (assert the emitted JSON carries `"line":8`, not the fn header) was
  removed rather than left failing.
- The COLL diagnostics on the LSP/MCP surface are presumably not reachable on
  this binary at all. That is a separate defect with a wider blast radius than
  this lane and is NOT claimed fixed here.
- The three-line position change is syntactically ordinary (`val x = if c: a
  else: b`, used throughout the tree) and mirrors the verified CLI change, but
  nobody has run it. Re-verify it when the parse failure above is fixed.
