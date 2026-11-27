# Non-discriminating (vacuous) spec family — enumerated sweep
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-08-08
**Status:** Open — detector landed, top findings proven, remediation outstanding.
Pre-push sweep reliability fixed 2026-08-09 (see update below): full sweep now
completes in ~1m35s with a real PASS verdict (was ERRORing every run, ~6-9min,
due to scanning gitignored `build/` scratch worktrees).
**Pinned base:** `f6397d726afde9f899cbfbc2dc8aa642bf764b21`
**Corpus:** 19,499 `*_spec.spl` files at that sha
**Detector:** `scripts/check/check-vacuous-specs.shs`

## 2026-11-03 detector lexical repair (family remediation remains open)

The current detector had a reproducible Tier-A false negative: assertion-like
text inside an ordinary quoted fixture counted as an executed assertion.
A two-file independent corpus contained only quoted `expect(...)`,
`assert_true(...)`, and local `check(...)` calls inside its spec bodies.
The original detector passed its eight self-tests and reported **2 files
scanned, 0 flagged**, although neither spec body executed any assertion.

The detector now masks quoted contents while retaining character positions
for raw balanced-argument extraction. Builtin, local-helper, assertion-subject,
failure-stub and constant-assertion lookup use those tokens. Actual assertions
keep their original quoted arguments for literal, matcher and tautology checks.
Both quote styles, backslash escapes and embedded comment markers are covered.

Four added self-test fixtures bring the gate to **12/12**: quoted builtin text
must produce V0 and V1; a quoted asserting-helper name must produce V1; real
computed assertions containing assertion-shaped fixture strings must stay
clean; and quoted fail text inside an ordinary helper must produce V0/V1
rather than count as an assertion or V6 stub.

Executed evidence on Windows through Git Bash, without a Simple seed:

- Updated detector: **12/12 self-test fixtures pass**, followed by the same
  independent two-file corpus producing **3 findings** (V1 for the quoted
  helper, V0 plus V1 for the quoted builtins).
- An isolated mutant removing quote masking from builtin/helper recognition
  is rejected by five new fixture expectations; it prints
  `SELFTEST FAILED` and `ERROR — nothing was checked`, with nonzero exit.
- Shell syntax and whitespace checks pass.

This verifies the shell detector change, not the Simple specs as behavioral
tests. No broad corpus sweep or semantic Tier-B qualification was performed.
The historical family remediation below remains open; this is not evidence
that all previously flagged specs discriminate correctly.

## Why

Four non-discriminating specs were found in a single day, each passing
identically on broken and fixed code: `try_operator_error_propagation_spec.spl`
(6/6 green on both, its own NON-VACUITY comment false), the named-ctor
regression spec (all args in field order, so a positional binder passes too),
the chunked-HTTP boundary spec (14 examples, zero hostile inputs, on a parser
that later yielded a request-smuggling overflow), and the LaTeX range spec
(`to_contain("n")` only, `int` half untested).

That is a family, not four coincidences. This document enumerates it and ships a
repeatable detector.

## Headline result

**All 86 examples of `test/01_unit/compiler/hir/hir_types_spec.spl` execute and
pass while asserting only `expect true`, with the module under test never
imported.**

```
SPEC FILE VERDICT: test/01_unit/compiler/hir/hir_types_spec.spl \
  declared>=86 executed=86 passed=86 failed=0 dropped=0
Results: 86 total, 86 passed, 0 failed
```

The file's real assertions are commented out and the import is commented out:

```
# TODO: Enable when hir module is ready for import
# use std.hir.{TypeId, BinOp, UnaryOp, DispatchMode, CaptureMode}

    it "void_ty returns id 0", tag: ["skip"]:
        # expect TypeId.void_ty().id == 0
        expect true
```

Note `executed=86`, not `dropped=86`: the `tag: ["skip"]` is **not** honored —
these examples really run and really report green. 86 green examples certify the
compiler's HIR type system and observe nothing.

## Detector methodology

Two tiers. Only Tier A is mechanized; that split is deliberate.

### Tier A — syntactic, decidable without semantics

| Code | Signal |
|------|--------|
| `V0_NO_ASSERT_FILE` | file contains zero assertion calls |
| `V1_ZERO_ASSERT` | an `it` block whose body asserts nothing |
| `V2_CONST_ASSERT` | straight-line block where every assertion subject is a constant expression |
| `V3_TAUTOLOGY` | `expect(X).to_equal(X)` — same expression both sides |
| `V4_WEAK_CONTAIN` | `to_contain("<=3 chars")` as a block's only assertion |
| `V5_SHAPE_ONLY` | block asserts only `.len()`/`is_empty`/truthiness, never content |
| `V6_STUB_HELPER` | block's only assertion routes to a `fail("TODO")` helper stub |

### Tier B — input-shape claims, MANUAL BY DESIGN

Inputs that never exercise the failure mode the spec claims to gate: all
happy-path inputs on a parser; arguments supplied in declaration order when the
bug is about order; exactly-divisible dimensions when the bug is about
remainders. **Three of the four seed cases were Tier B.** Detecting these
requires knowing what the bug was, so mechanizing them produces noise that must
be hand-triaged anyway. Apply this checklist manually to the high-risk shortlist:

1. Does any input violate the invariant the spec claims to protect?
2. If the bug is about *order*, does any example use non-declaration order?
3. If the bug is about *remainders/boundaries*, is any input non-exact?
4. On a parser over untrusted input, is any input hostile/malformed/truncated?
5. Does the spec's own "non-vacuity" comment, if present, actually hold?

### Two rules that required semantic care

The naive versions of these produced large false-positive classes, both found by
sampling before publishing any count:

- **Helper delegation.** 3,560 corpus files wrap the assertion in a local helper
  (`fn check(c): expect(c).to_equal(true)`). Treating `check(x)` as "no
  assertion" produced ~12 false `V1` hits per file. The detector now resolves
  local helper fns to whether they ultimately assert (2 rounds, so
  helper-calls-helper resolves).
- **Constant assertions are only vacuous in straight-line blocks.** In
  branch-coverage specs, `check(true)` in one arm is paired with `check(false)`
  in the other, so a wrong branch genuinely fails. `V2` therefore fires only when
  the block has **no control flow** and **every** assertion subject is a constant
  expression (`1 == 1`, `"a" == "a"`, `true`). Fixture F7 guards this exemption.

### Empirically-corrected assertion vocabulary

`expect` also has a **paren-less statement form** — `expect diagram_args.len() ==
3`, and after a match arm `case nil: expect false`. It is a registered builtin of
arity 1 (`src/compiler/30.types/type_system/builtin_registry.spl:155`).

**This form does assert** — probe result: a spec containing only `expect false`
reports `executed=2 passed=0 failed=2`, exit 1. Missing it made `V1_ZERO_ASSERT`
fire falsely on real assertions across 1,322 files (33,564 uses). Correcting it
dropped `V1` from 1,300 files to 251 and `V0` from 1,181 to 232.

### Fail-closed design and injection-test proof

This repo has a documented history of sweep oracles failing open. The detector
runs `--selftest` **before every scan, fatally**, over 8 fixtures:

| Fixture | Shape | Must |
|---------|-------|------|
| F1 | `expect(true).to_be_true()` | FLAG |
| F2 | exact `to_equal` on a computed value | not flag |
| F3 | vacuous assertion **not on line 1**, valid content above | FLAG — catches an anchored regex without a multiline flag matching only line 1 |
| F4 | spec at a **deep nested path** | FLAG — catches a path filter missing the tree prefix reporting "0 candidates" as a clean sweep |
| F5 | helper-delegated **real** assertion | not flag |
| F6 | straight-line block, all assertions constant expressions | FLAG |
| F7 | branch-coverage `check(true)`/`check(false)` | not flag |
| F8 | paren-less `expect <expr>` on a computed value | not flag |

Negative controls verified (the selftest can actually fail):

- Sabotaging `has_assert` to always return 0 → `SELFTEST FAILED … refusing to
  scan`, exit 2.
- Empty root → `ERROR — nothing was checked`, exit 2. A zero-candidate sweep is
  never a pass.
- Nonexistent root → exit 2.
- `scanned` is summed across **all** `xargs`-split awk invocations and reconciled
  against the listed file count; a mismatch is `ERROR`, not a partial pass.

Verdict is always the last line: `PASS — <n> files scanned, <m> flagged`.

## Results at the pinned sha

`PASS — 19499 files scanned, 33568 flagged`

| Code | Rows | Files |
|------|------|-------|
| `V2_CONST_ASSERT` | 25,406 | 3,427 |
| `V5_SHAPE_ONLY` | 2,276 | 1,023 |
| `V4_WEAK_CONTAIN` | 2,180 | 547 |
| `V1_ZERO_ASSERT` | 1,995 | 251 |
| `V3_TAUTOLOGY` | 1,449 | 343 |
| `V0_NO_ASSERT_FILE` | 232 | 232 |
| `V6_STUB_HELPER` | 30 | 6 |
| **distinct files** | | **5,428** (27.8% of corpus) |

`test/unit/` and `test/01_unit/` (likewise `system`/`03_system`,
`integration`/`02_integration`, `perf`/`05_perf`) are **byte-identical mirror
trees**, so every finding is counted twice. **Collapsing mirrors: 3,150 distinct
specs.**

### On the prior 22,039/15% vs 513-examples/45-files contradiction

**Neither figure is reproducible, because neither names a base commit**, and the
task was right not to treat either as settled. This sweep supports *neither*
directly. What this sweep states, with the base pinned:

- **3,150 distinct specs (5,428 counting mirrors) carry at least one Tier-A
  syntactic vacuity candidate** at `f6397d72`.
- That is **candidates**, not proven-vacuous specs. Only the subset below is
  empirically proven. Conflating those two claims is how the earlier numbers
  became unusable, so they are reported separately here.

`origin/main` moved **three times during this session** (`1c04408` → `0c4d480` →
`f6397d7`), which is why an immutable sha, not a moving ref, is the base.

## Risk-ranked findings

Ranked by what a green verdict falsely certifies, not by how vacuous it looks.
Mirror duplicates collapsed.

| # | Spec | Vacuous blocks | Gates | Risk | Proof |
|---|------|---------------:|-------|------|-------|
| 1 | `test/{01_,}unit/compiler/hir/hir_types_spec.spl` | 86 | compiler HIR type system | **critical** | PROVEN: 86/86 green, import commented out |
| 2 | `test/{01_,}unit/compiler/hir/hir_eval_spec.spl` | 82 | compiler HIR evaluation | **critical** | PROVEN: 82/82 green |
| 3 | `test/{01_,}unit/compiler/hir/hir_module_spec.spl` | 59 | compiler HIR module | **critical** | candidate, same shape |
| 4 | `test/{01_,}unit/compiler/hir/hir_lower_spec.spl` | 56 | HIR→MIR lowering | **critical** | candidate, same shape |
| 5 | `test/{01_,}unit/compiler/parser/treesitter_parser_real_spec.spl` | 41 | parser core ("Real Implementation Tests") | **critical** | candidate; assertions commented out, Status: Planned |
| 6 | `test/{01_,}unit/compiler/parser/treesitter_lexer_real_spec.spl` | 38 | lexer core | **critical** | candidate, same shape |
| 7 | `test/{feature,03_system/feature}/usage/parser_declarations_spec.spl` | 19 | parser declarations | high | candidate |
| 8 | `test/03_system/feature/compiler/bootstrap_system_spec.spl` | 14 | bootstrap/self-host | high | candidate |
| 9 | `test/{feature,03_system/feature}/usage/parser_skip_keyword_spec.spl` | 11 | parser keyword handling | high | candidate |
| 10 | `test/01_unit/os/compositor/compositor_occlusion_spec.spl` | 10 | OS compositor occlusion | high | candidate |
| 11 | `test/01_unit/compiler/frontend/parser_spec.spl` | 10 | frontend parser | high | candidate |
| 12 | `test/{01_,}unit/std/deep/dict_deep_4_spec.spl` | many | claims "STDLIB Deep-Dive / dict"; asserts `check(1 == 1)`, `check("a" == "a")` | med-high | candidate; body contains no dict symbol |

**900 `V2` files sit in high-risk domains** (compiler / parser / os / codegen /
crypto / net / memory) after excluding other lanes' paths.

### The dominant sub-family: commented-out assertion + live `expect true`

**51 files** have both a commented-out assertion and a live constant-assert
block; **25 of them are in high-risk domains**. This is the single most
productive pattern: an assertion was disabled pending a module, replaced with
`expect true`, and the spec kept reporting green ever since. Findings #1–#9 are
all this shape.

The `hir_*` family alone is **283 green examples per mirror tree (566 total)**
certifying the compiler's own HIR while importing nothing.

## Off-limits (other lanes own these)

Excluded from ranking and remediation, listed so the enumeration stays complete:
`try_operator_error_propagation_spec.spl`; the named-ctor regression spec; the
chunked-HTTP specs; the LaTeX range spec; AES/crypto specs; `struct_field_order`;
the shape-(d) refactor family.

## Reproducing

```sh
sh scripts/check/check-vacuous-specs.shs --selftest          # 8 fixtures, fatal
sh scripts/check/check-vacuous-specs.shs --root . --tsv      # full sweep
```

Pin the corpus first for a stable count:

```sh
git archive <sha> $(git ls-tree -r --name-only <sha> | grep '_spec\.spl$') | tar -x -C /tmp/pin
sh scripts/check/check-vacuous-specs.shs --root /tmp/pin --expect-files 19499 --tsv
```

## Harness caveat observed

A one-line trivially-passing spec under `src/lib/**/test/` reports `SPEC FILE
VERDICT … passed=1 failed=0` while also printing `Results: 0 passed, 1 failed`
and exiting 1. Another lane is root-causing this; findings here avoid that path.
Not attributable to this sweep.

## Strengthened so far

### `test/{01_,}unit/std/deep/dict_deep_4_spec.spl` — DONE, discrimination proven

A file titled "STDLIB Deep-Dive Test", Category "Standard Library Deep Coverage",
Status "Implemented", named `dict_deep_4`, whose first 16 examples asserted pure
arithmetic constants — `check(1 == 1)`, `check("a" == "a")`, `check(5 - 3 == 2)`,
`check(true and true)` — and whose `dict 2` example bound `val d = {}` and then
asserted `check(true)`, ignoring the dict entirely. It covered no dict behavior.

Rewritten: 11 real dict examples (read-back, key distinctness, presence/absence,
`keys().len()`, empty dict, duplicate-key overwrite, **stored zero vs absent key**,
case sensitivity, empty-string key, text values, keys()/contains_key agreement),
plus `dict 2` and `nested 1` given real oracles. Assertions honor
`doc/07_guide/language/dict_native_pitfalls.md`: no `Dict.len()`, no `.get()` —
`keys().len()` and index reads / `contains_key` only.

**Discrimination control (sabotage-and-restore on the oracle):**

| Control | Result |
|---------|--------|
| A — as written | `executed=38 passed=38 failed=0 dropped=0`, exit 0 |
| B — 4 independent oracles mutated to wrong values | `executed=38 passed=34 failed=4 dropped=0`, exit 1 |

Exactly 4 mutations produced exactly 4 failures, one-to-one. The original
constant assertions could not have produced a single one. Mutation was performed
on a scratch copy, leaving the shared working copy untouched.

**Detector before/after on the same file:** original pinned version → 17 flagged;
strengthened version → 0 flagged.

## Remediation

1. The `hir_*` family (#1–#4) and `treesitter_*_real` (#5–#6) must either import
   and assert against the real module, or be marked failing per
   `.claude/rules/testing.md` ("a correct spec that fails is a legitimate
   artifact"). They must not keep reporting green.
2. Wire `check-vacuous-specs.shs` into the pre-commit/CI check set so new
   `expect true` placeholders cannot land silently.
3. Work the remaining 900 high-risk `V2` files by descending block count.
4. Apply the Tier-B manual checklist to the high-risk shortlist.

## 2026-08-09 update — pre-push run was never actually completing; root cause + fix

The guard is wired into the pre-push hook
(`scripts/check/pre-push-conflict-tree-guard.shs` → `run_guard
"$vacuous_specs_guard" ...`, "full scan, not range-bound"). A prior session
reported it "too slow to finish within budget; selftest passed, full sweep
inconclusive" — i.e. no one had actually gotten a completed verdict from a
full sweep since it landed the day before.

**Root cause was not raw slowness — it was scan scope.** `find "$ROOT" -name
'*_spec.spl'` with `ROOT=.` walked into `build/`, which is gitignored (see
`.gitignore`, CLAUDE.md "Owned-Code Scope") and holds parallel-agent-session
scratch checkouts such as `build/worktrees/simpleos-engine2d-stage4-snapshot/`
— a **full mirror of `test/`**, and therefore of every `*_spec.spl` in the
real corpus. Before the fix: **107,169** files "listed", of which **81,833
(76%)** were under `build/`. Two consequences:

- **~4-6x inflated runtime.** Two timed full runs before the fix: 6m30s and
  9m01s wall-clock (363–415s user CPU either way — the wall-clock spread is
  this shared host's concurrent load, not the script).
- **Every run ERRORed, never PASSed or FAILed.** The `build/worktrees/*`
  scratch tree is *live* — another agent session creates/deletes/rewrites
  files in it while the sweep runs — so the guard's existing (correct)
  fail-closed reconciliation (`scanned` count vs files `find` originally
  listed) tripped on real races in genuinely-ephemeral files, every time:
  `scanned=107168 but 107169 files were listed`, `scanned=107165 but 107166 …`.
  These were legitimate ERRORs by the code as written — the bug was scanning
  gitignored scratch as if it were the corpus, not the reconciliation logic
  itself.

**Fix (`scripts/check/check-vacuous-specs.shs`):**

1. `find` now prunes `build/` and `.git/`:
   `find "$ROOT" \( -path '*/build/*' -o -path '*/.git/*' \) -prune -o -name
   '*_spec.spl' -type f -print`. (`git ls-files` was tried first as a more
   "principled" fix and reverted: in this actively-mutating shared working
   copy the git **index** itself lists ~3,100 paths that are not currently on
   disk — e.g. a concurrent session's `rm` without `git rm` — which traded one
   staleness problem for a worse one. Pruning the one directory that is
   actually the scratch offender is more targeted.)
2. The scanned-vs-listed reconciliation is now per-file, not count-only: the
   awk program emits a `#FILE\t<path>` marker for every file it actually
   opens, the shell diffs that against the snapshot list, and a missing file
   is only a real `ERROR` (ungenuinely-unscanned, i.e. it still exists on disk
   but the scan skipped it) — a file that no longer exists at reconciliation
   time was legitimately dropped by a moving target and is excluded from the
   required count instead. This is strictly more precise than before, not
   weaker: every file that still exists still gets scanned and still counts.

**Verified after the fix** (today, live corpus, `sh
scripts/check/check-vacuous-specs.shs`, no `--root`):

- `--selftest`: 8/8 fixtures still behave correctly (unchanged).
- Two consecutive full runs: **25,312** then **25,313** files scanned (the
  +1 is a real concurrent edit between runs, not drift/error), **45,486**
  flagged both times, wall-clock **1m35s** and **1m41s**, exit 0.
- Verdict: **`PASS — 25313 files scanned, 45486 flagged`.**
- By code (today, unpruned mirrors — `test/unit` vs `test/01_unit` etc. still
  double-count as documented above):

  | Code | Rows |
  |------|-----:|
  | `V2_CONST_ASSERT` | 37,059 |
  | `V5_SHAPE_ONLY` | 2,301 |
  | `V4_WEAK_CONTAIN` | 2,230 |
  | `V1_ZERO_ASSERT` | 2,164 |
  | `V3_TAUTOLOGY` | 1,463 |
  | `V0_NO_ASSERT_FILE` | 239 |
  | `V6_STUB_HELPER` | 30 |

  Row counts are higher than the 2026-08-08 pinned-sha table (33,568 total)
  because the corpus has grown since `f6397d72` (19,499 → 25,313 files) — not
  a detector regression; `--root . --expect-files 19499` against a pinned
  archive of that sha would reproduce the original count exactly, as
  documented above.

**Not fixed / explicitly out of scope for this pass:** the guard has **no
fail-on-findings gate at all** — `exit 0` with a `PASS —` line is
unconditional once the sweep completes cleanly, regardless of how many
`V0`–`V6` findings it reports. Its fail-closed contract (per its own header)
is about the *sweep's own reliability* (did it actually examine the claimed
corpus), not about blocking a push over pre-existing vacuous specs — turning
45,486 pre-existing findings into a hard gate would brick every push and is a
separate, much larger remediation decision (tracked above under
"Remediation"), not a silent side effect of a perf/scoping fix. Left
unchanged, per instructions not to weaken *or* strengthen detection semantics
as a side effect of a reliability fix.

## Triage 2026-09-13 (BUGFIX-10 fanout)

Re-ran `sh scripts/check/check-vacuous-specs.shs --selftest`: still
`PASS — selftest only, 8 fixtures checked, 0 flagged in corpus` (8/8 fixtures
correct). Detector remains healthy and wired into the pre-push guard. The
remaining remediation items (#1-4 in "Remediation" above — rewriting the
`hir_*`/`treesitter_*_real` spec families with real assertions, working the
~900 high-risk `V2` candidates, wiring a hard gate) are each independently
large, cross-cutting efforts well beyond a single 45-minute bugfix-lane
change and touch specs other lanes may be actively editing. No remediation
attempted this pass; leaving OPEN as filed.
## Triage 2026-09-13

Large audit/remediation effort: a 19,499-spec corpus sweep with a
landed detector but outstanding remediation across many individual
vacuous specs (the headline example alone is an 86-example spec file
needing its commented-out module import and assertions restored, which
requires the target module to actually be import-ready). Not a single
localized bug; out of this lane's per-item budget. Leaving OPEN.



## 2026-11-05 re-check of the headline finding (origin/release/1.0.0 4397a4ce3c6)

Premise still holds: `test/01_unit/compiler/hir/hir_types_spec.spl` still has
86 `expect true` bodies (all real assertions and the `use std.hir.*` import
commented out). Root cause for why it cannot simply be re-enabled: `TypeId`
(`void_ty`, `i64_ty`, `nil_ty`, `is_void`, ...) is not defined under
`src/lib` or `src/compiler`; the only Simple definitions live in the Rust-side
std copies `src/compiler_rust/lib/std/src/hir/{eval,lower,module}.spl`, and the
live Rust type is `TypeId(pub u32)` in
`src/compiler_rust/compiler/src/hir/types/type_system.rs`. `std.hir` therefore
does not resolve from the self-hosted tree.
Remediation needs an owner decision (port the TypeId surface to
`src/compiler/20.hir` and rewrite the spec with real assertions, or delete the
spec as covering a nonexistent module). No spec was changed in this slice.
The family remediation remains OPEN.

## 2026-11-06 owner decision — port TypeId, rewrite hir_types_spec (headline finding remediated)

**Decision (2026-11-06, owner decision):** port the TypeId surface used by
`hir_types_spec.spl` into the Simple sources and rewrite the spec's 86
`expect true` placeholders as real, discriminating assertions (rather than
deleting the spec).

Done on branch `work/hir-typeid-port`:

- Ported the HIR type model (`TypeId`, `BinOp`, `UnaryOp`, `DispatchMode`,
  `CaptureMode`, `LocalVar`, `CapturedVar`, `HirExprKind`, `HirStmtKind`,
  `HirPatternKind`, `HirLiteral`, `HirExprNode`, `HirStmtNode`) from
  `src/compiler_rust/lib/std/src/hir/types.spl` to
  `src/lib/common/hir/types.spl` (`use std.common.hir.types.{...}`); it is pure,
  allocation-free and panic-free (total `match`es, no indexing).
- Rewrote `test/01_unit/compiler/hir/hir_types_spec.spl`: 0 `expect true`, no
  `skip` tags, live import, and every predicate case pairs the positive with a
  negative/neighbour case. 96 examples.
- Evidence (seed `bin/simple.exe test`, Windows): RED before the port —
  `outcome=ERROR declared>=96 executed=0`; GREEN after —
  `outcome=OK executed=96 passed=96 failed=0`. Mutation check: forcing
  `TypeId.is_void()` to `true` turns it to `passed=95 failed=1`.
  `check-vacuous-specs.shs --root <dir>`: old spec `86 flagged`, new spec
  `0 flagged`.
- **Real defect the rewritten spec found (would have stayed hidden under
  `expect true`):** `TypeId.name()` returned `type_0`/`type_1`/... for every
  primitive in the spec lane. Root cause: the seed interpreter's literal
  pattern matcher (`src/compiler_rust/compiler/src/interpreter_patterns.rs`,
  `Pattern::Literal` → `Expr::Integer` arm) only matches `Value::Int`, so a
  `u32`-typed subject (field or `val x: u32`) never hits an integer arm in the
  spec lane, even when passed through an `i64` parameter (`bin/simple.exe run`
  does not reproduce it). Worked around in the port with `match self.id as
  i64`; the seed matcher gap itself remains open and is recorded here as a
  concrete seed bug (unsigned-int subject vs integer literal pattern).

The family (other flagged specs) remains OPEN; only the headline
`hir_types_spec` finding is remediated.


## 2026-11-08 detector comment/docstring lexical repair (partial family)

The current detector's pass0 toggled raw triple-quote substrings before
stripping ordinary comments. A valid `# """` comment therefore entered docstring
mode and hid following real assertions. An independent two-file corpus differing
only by that comment produced V0 and V1 for the comment variant, while its
otherwise identical computed-assertion control stayed clean.

Pass0 now scans lexical context once: line comments and ordinary quoted tokens
cannot open docstrings; both triple quote styles mask their body; code after a
real closing delimiter survives. It keeps original source positions. The triple
closing rule matches the actual core lexer (`lexer_struct.scan_string` and
`scan_raw_string`): triple-string bodies are literal, so a matching delimiter
closes even after a backslash. The initial 19-fixture revision did not discriminate the new slow-path escape
branch; the review correction below adds that missing coverage.
The assertion classifier, finding vocabulary, scan policy and existing baselines
are unchanged.

Seven new fixtures extend the detector selftest from 12 to 19: comment delimiters,
quoted delimiter data with escapes/comment markers, real double- and single-
quoted multiline documentation, inline closing followed by real assertion code,
raw-triple backslash closing, and a trailing comment that must not hide the next
zero-assertion example. The single-triple and trailing-comment cases also prevent
false clean reports, beyond the original false positive.

Executed on Linux/aarch64 using the shell/AWK detector, pinned to CPU 16:

- 19/19 selftest fixtures pass for each of two implementation revisions; the
  second adds bounded fast paths to avoid character-scanning ordinary lines and
  real docstring body lines. No unchanged green check was repeated.
- Restoring exactly the old pass0 in an isolated mutant makes the new selftest
  reject it with `SELFTEST FAILED` and exit 2. It catches the comment/quoted-data
  false positives and the single-doc/post-doc-comment false negatives.
- The original independent two-file corpus now has 0 V-code findings, scanned 2.

Retained local evidence: `/tmp/p2-vacuous-evidence-20261108/receipt.json`,
`mutant.log`, `independent-probe.log`, and
`/tmp/p2-vacuous-selftest-20261108.log`.

This qualifies the narrow shell detector repair. It does not execute any Simple
spec, perform a broad corpus sweep, establish Tier-B semantic discrimination,
or remediate the remaining vacuous specs. The family remains partial and
verification pending; no fixed/closed mark or compiler/bootstrap qualification
is claimed.

The final revision retains index-based fast paths for ordinary corpus lines and
uses the lexical character scan only where a triple marker is present. A single
bounded 410,924-byte / 2,000-example synthetic comparison produced identical
findings: baseline 0.16 s / 8,204 KiB max RSS, new 0.18 s / 9,964 KiB. This small one-shot
signal is not a statistically established performance delta; whole-corpus
throughput/RSS remains an explicit followup, not a claimed speedup. The exact
old-pass0 mutant was again rejected against the final revision.


## 2026-11-08 review correction — discriminate slow raw/escape branches

Opus source review found no production defect, but returned FAIL because the
initial 19 fixtures did not execute both `raw_q` and short-string escape branches
on triple-marker lines. The escaped line took the old fast path, and the raw
triple fixture bypassed the short-string branch. Those cases were not adequate
proof of the new branch behavior.

Three valid lexical fixtures now bring the total to 22. Each places an opposite-
quote triple marker on the same line as the relevant short token, forcing the
slow path. Double-quoted and single-quoted ordinary strings use an escaped
matching quote followed by the opposite triple marker; those markers remain
string data. A short raw `r"C:\"` token closes at its first quote after the
backslash and is followed by an actual multiline string containing fake
assertion text. Both quote styles process backslash escapes in the real
`src/compiler/10.frontend/core/lexer_struct.spl:scan_string`; raw short strings
and the bare `r` prefix are owned by `scan_raw_string` and `scan_ident`.

The production AWK program is byte-identical to `cdc389ee302`; only selftest
fixtures/counters/messages and evidence changed. Actual detector selftest:
22/22 PASS, executed once after the fixture change. Four isolated mutants are
all rejected with `SELFTEST FAILED` and exit 2: force `raw_q=0`, force `raw_q=1`,
delete the slow escape branch, and restore the original pass0. The first three
specifically fail the new F20/F21/F22 assertions; they cannot silently pass via
the fast path.

Durable final evidence is committed under `.spipe/p2_vacuous_lex_20261108/`:
`receipt.sdn`, `selftest-cycle3.log`, and the four `*-cycle3.log` mutant outputs.
Earlier `/tmp` paths above are historical local evidence, not the durable final
receipt. This still proves shell-detector behavior only. No Simple fixture
execution, production corpus scan, compiler/native build, or umbrella closure
is claimed. Required Opus re-review remains pending; the previous FAIL is not
converted to PASS by these local tests.
