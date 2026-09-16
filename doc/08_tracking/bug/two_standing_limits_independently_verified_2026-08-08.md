# Two "standing limits" independently re-verified: shape-(d) 42/29 is stale; lexer harness DOES emit a verdict

- **Filed:** 2026-08-08
- **Context:** both numbers had been repeated in summaries without independent
  verification — one because a spot-check reviewer explicitly said counts and
  spot-checks are different claims, the other because a harness invocation
  reportedly burned >25 minutes with zero verdict. Re-verified from scratch
  against `origin/main` (not the shared WC, which carries ~10 sessions'
  in-flight edits) in an isolated `git archive` checkout.

## Number 1 — shape-(d) survivor count: "42 / 29" is superseded, not current

The "64 -> 42, 29 real defects" figure comes from commit `9d4d16b106e`'s own
commit message ("STATUS: 42 oracle hits remain ... so 29 are actual family
survivors"). That number is **already stale by the time it was quoted**: the
SAME tracking doc
(`doc/08_tracking/bug/impl_to_free_fn_refactor_family_still_incomplete_2026-08-08.md`)
was updated again same-day ("session 2") after an extraction-bug fix and 10
more restores, landing on **43 raw hits -> 33 raw hits**, of which the doc
itself classifies only **5-6 as genuine remaining family damage** (Class B,
deliberately unfixed — semantics would have to be invented), the rest being
Class C (not this family) or catalogued regex false positives (docstrings,
`me fn`, import aliases, embedded shader source).

**Independent reconstruction (this session), against `origin/main` tip
`d080bcb8dce`, `git archive`'d into an isolated tree (not the shared WC):**

- Rebuilt the oracle verbatim from the doc's own shell one-liners (fail-closed
  definition-existence check: `grep -rEoh '\b(fn|me)[[:space:]]+[a-zA-Z0-9_]+'`
  over `src/` for definitions, cross-referenced against the two backreferenced
  call-shape regexes for call sites), using `/usr/bin/grep -r` (not `-R`, not
  wrapped `grep`) so the `mir`/`hir`/`driver`/`backend` symlinks under
  `src/compiler/` are not double-counted.
- **Result: 33 raw oracle hits** — matches the doc's own session-2 number
  exactly, not 42.
- Breakdown of the 33: 7 previously-catalogued false positives (`me fn`
  blind spot x2, embedded MSL shader x1, docstring text x4) + 11
  docstring/example false positives + 1 import-alias false positive + 8
  Class C (7 `fuzz.spl` missing-module sites, 1 `sys_exit` stdlib gap) + **6
  genuine remaining family survivors**: `template.spl:165`,
  `effects.spl:117,353,361`, `recovery.spl:215`, `blocks/testing.spl:294`.
  7+11+1+8+6 = 33, reconciling exactly.
- **Injection-tested in both directions**: appended a call to a fabricated
  symbol (`zzzinjected_probe_thing_test`) — survivor count moved 23 -> 24
  unique names and the injected name was correctly flagged; reverting
  restored the byte-identical 33-hit survivor list. A known-defined symbol
  (`markedident_add_mark`) is correctly excluded (0 hits).

**Verdict: "42 / 29" was already superseded within the same document before
anyone quoted it downstream — the correct, current, independently-confirmed
figures are 33 raw oracle hits / 6 real remaining family-damage sites (Class
A mechanical restores are fully closed; Class B is deliberately unfixed
pending a semantics decision).** Neither the sweep author nor the spot-check
reviewer was wrong about what they each checked; the "29" simply wasn't the
doc's own latest number by the time it got repeated.

## Number 2 — lexer radix-literal-suffix matrix: the harness DOES emit a verdict

Ran `test/01_unit/compiler/lexer/lexer_radix_literal_suffix_spec.spl`
(from `b0f5308993`, present on `origin/main` but not in the shared WC's
current HEAD lineage) with `bin/simple test <spec> --no-session-daemon`
against an isolated `origin/main` checkout (not the shared/contended WC):

```
9 examples, 0 failures
SPEC FILE VERDICT: test/01_unit/compiler/lexer/lexer_radix_literal_suffix_spec.spl declared>=9 executed=9 passed=9 failed=0 dropped=0
PASS ... Duration: 388ms
```

**Injection test:** swapped `src/compiler/10.frontend/core/lexer_struct.spl`
for its pre-fix parent (`b0f5308993^`) and re-ran the identical spec —
5 of 9 examples fail, exactly the binary/octal-suffix and 64-bit
underscore-run cases the fix addresses:

```
9 examples, 5 failures
SPEC FILE VERDICT: ... executed=9 passed=4 failed=5 dropped=0
FAIL
```

Restoring the post-fix file returns byte-identical content and the 9/0
verdict. Round-trip clean.

Also spot-checked the two structural claims directly in source (not by
construction, by reading):
- `make_token` -> `core_token_suffix_save` ordering is preserved in the
  0b/0o branches, matching the pre-existing hex/decimal branches
  (`lexer_struct.spl:519-524`, `569-572`, `611-614` vs `:708-709`).
- Both literal-parsing consumers route through the radix-aware
  `parse_int_literal_text` (`_ParserPrimary/primary_expr.spl:156,353,365`).

**Verdict: the harness ran cleanly and emitted a real, injection-tested
verdict in well under a second — it did not reproduce the ">25 minutes /
zero verdict" failure.** That symptom is most likely a shared/contended-WC or
missing-`--no-session-daemon` artifact, not a property of this spec. Filed a
reusable fence at `scripts/check/check-lexer-radix-literal-suffix.shs` (exit
0 = PASS with 0 failed/dropped, exit 2 = harness non-emission reproduced —
do not treat silence as a pass) so this doesn't need re-deriving.

## Method notes

- Both checks ran against a `git archive origin/main` extraction into
  `/tmp` — the shared WC was never modified for either check apart from a
  reversible swap of one file for its parent-commit content, restored
  byte-identical and verified with `diff` before moving on.
- `/usr/bin/grep -r` used throughout for load-bearing counts, not the
  wrapped `.gitignore`-honouring `grep`.
- Test trees are not duplicated for either number: the shape-(d) oracle
  scans `src/` only (no `test/`), and the lexer spec lives at
  `test/01_unit/compiler/lexer/...` — the `test/unit/...` mirror does not
  contain this file (checked, absent).

## Related

- `doc/08_tracking/bug/impl_to_free_fn_refactor_family_still_incomplete_2026-08-08.md`
- `doc/08_tracking/bug/impl_to_free_fn_refactor_family_sweep_2026-08-07.md`
- `doc/08_tracking/bug/lexer_binary_octal_literal_suffix_split_and_digit_cap_2026-08-08.md`
- `scripts/check/check-lexer-radix-literal-suffix.shs`
