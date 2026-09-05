# Parser Sharing — Measured Audit and Next Shared Seam (contract v1)

**Date:** 2026-09-05 · **Status:** audit complete; Seam 1 and Seam 3 landed in this worktree, Seam 2 proposed
**Worktree:** `/home/yoon/dev/simple-parser-sharing` — a LINKED git worktree
(shared object store), detached at `67859c96792`, which was `main`'s tip at
2026-09-05 15:10 and has since advanced
**Audited state:** the `main` working copy at `/home/yoon/dev/simple` on
2026-09-05, *including* Codex's 38 uncommitted modified files and its untracked
`structural_adapter/`, `lexer_tape.spl`, `canonical_adapter.spl` work. The
worktree is at the committed tip and therefore does **not** contain that work;
it exists so this lane can add files without touching Codex's dirty set.

**Lane etiquette.** `doc/03_plan/agent_tasks/parser_framework.md` freezes the
merge contract and forbids editing another lane's dirty files. Every parser file
named in Part 1 is in Codex's dirty set and none was edited. The work in Part 2
therefore lands only in files that are clean at HEAD or newly created. The merge
owner (Codex) and final reviewer (Astra) decide adoption.

---

## Part 1 — Claimed vs. measured

`doc/03_plan/agent_tasks/parser_framework.md` § "Current sharing completion
matrix (2026-09-05)" marks seven boundaries. Re-measured by grep over `src/`
(`*.spl`, production only — `test/` excluded):

| Boundary | Claim in matrix | Measured | Verdict |
|---|---|---|---|
| Compiler + core interpreter | landed | `ParseReceipt`/`parse_receipt_from_text` imported by `frontend.spl`, `core/frontend.spl`, `_FlatAstBridge/module_assembly.spl` | **Confirmed** |
| App interpreter | landed acceptance slice | `canonical_adapter.spl` + `canonical_main.spl` present and specced | **Confirmed**, legacy REPL still outside |
| SHS | landed | suffix-only identity in `driver_source_loading.spl` | **Confirmed** |
| SDN | contract sharing only | `sdn/parser.spl:6` imports `ParseReceipt` and nothing else from the framework | **Confirmed, and correctly scoped** |
| CoreLexer structural adapter | landed lexical bridge | `structural_adapter/core_lexer_adapter.spl` has **zero production importers** — the only `src/` file naming it is itself | **Test-only.** "Landed" overstates it |
| CoreLexer token tape | foundation landed | `lexer_tape.spl` named only by itself, `core/__init__.spl` (re-export) and `lexer_types.spl` — **zero consumers** | **Test-only.** Matrix already says consumer parity is required; the word "landed" should not appear without a consumer |
| Tree-sitter outline | CoreLexer wrapper landed | `outline_lexer.spl` holds `lexer: Lexer`, so the *lexer* is genuinely shared; the outline's 314-line token facade is not | **Confirmed as a wrapper**, blocked per the filed bug |

**Answer to "does the Codex session share parser infrastructure?" — Yes, at the
contract layer, and the SDN/SHS/frontend receipt sharing is real and verifiable.
Two of its seven "landed" rows are test-only artifacts with no production
consumer, and the docs should say so.** No row overclaims shared *grammar*; the
plan explicitly refuses that claim, which is correct.

### Two measured defects behind the claims

**D1 — global parser source state survives, in the lexer itself.**

```
grep -rn "current_core_source_get\|current_core_source_set" src/ --include=*.spl
→ 8 sites in 2 files: core/lexer.spl, treesitter/outline_lexer.spl
```

The plan says migrated consumers "receive owner-bound diagnostics rather than
publishing parser globals after a call returns." True at the *consumer* layer;
the global is still the lexer's own source-of-truth, and
`treesitter_effective_source` reads it as a fallback. Until this reaches 0, two
parsers can disagree about which source they are looking at, and the
`SourceSnapshot` identity contract is advisory rather than enforced. The bug
record already documents one live symptom of this class (`lex_source_slice`
returning empty text against a span the wrapper reported as valid).

**D2 — the largest unshared Simple-source parser is outside the lane entirely.**

| File | Lines | Imports compiler lexer? |
|---|---|---|
| `src/app/spipe_docgen/spipe_docgen/parser.spl` | 1,939 | **No** — only `spipe_docgen.common` and `std.math_repr` |
| `src/app/sspec_maintain/source_facts.spl` | 578 | **No** — only `model` and `sha256` |
| `src/app/sspec_maintain/analyzer.spl` | — | **No** |

`spipe_docgen/parser.spl` parses `_spec.spl` — *Simple source* — with 255
`trim`/`starts_with`/`contains`/`split` call sites and hand-rolled
`count_leading_indent` / `strip_indent` / `dedent_lines`. It is a second,
line-oriented Simple front end reimplementing indentation and docstring rules
the CoreLexer already owns. It is not in the lane's owned paths
(`src/lib/common/structural/parse/`, `canonical_ast/`, `structural_adapter/`),
so no acceptance gate in the frozen matrix can ever see it.

This is the headline finding: **parser sharing is being measured only inside the
compiler, while the biggest duplicate Simple parser in the tree sits in
`src/app/` and is invisible to the lane.**

---

## Part 2 — Design: the next shared seam

Ordered by measured payoff, smallest first. Each is stated in the frozen
matrix's own format so the merge owner can paste it in.

### Seam 1 (ship first) — freeze the parser-source globals

| Lane | Owner | Deliverable | Acceptance gate |
|---|---|---|---|
| Source-identity ratchet | CoreLexer | `current_core_source_*` reachable only from the snapshot owner | `scripts/check/check-parser-source-global-ratchet.shs` PASS; baseline 8 never rises; every reduction re-baselined deliberately |

**Wired, advisory.** Per `.claude/rules/vcs.md`, a script with a baseline file
enforces nothing — a guard runs only as a `tier=push` row in
`config/check/must_check_gates.sdn` with a byte-matching case arm in
`run_manifest_push_gates`. Both are added, as `push_blocking: false`: a
brand-new gate records its verdict before it blocks. `check-guard-wiring.shs`
confirms the wiring (`0 NEW unwired`); its own FAIL is `1 copied hook(s)`, a
pre-existing linked-worktree hook artifact this lane did not touch. Promote to
blocking once it has ridden a few pushes green.

Rationale: 8 sites in 2 files is a closeable number, and freezing it converts
"parser globals were eliminated" from prose into a checkable verdict. The gate
is shipped with this document (see Part 3) precisely because it changes no
`.spl` file and therefore cannot collide with Codex's dirty set.

**Non-goal:** this gate does not remove a single global. It stops the count
growing while Codex's lanes land, and it makes the eventual removal visible.

### Seam 2 — give the tape and the adapter one production consumer each

| Lane | Owner | Deliverable | Acceptance gate |
|---|---|---|---|
| Tape consumer | CoreLexer | one production caller of `lexer_tape` outside `core/` | the matrix row may say "landed" only when `grep -rln lexer_tape src/ \| grep -v test` names a consumer |

A foundation with zero consumers has no parity pressure on it, which is how a
shared representation drifts from the thing it is meant to replace. The
Tree-sitter blocker record already states the tape is *not* the cause of the
outline defects — so the tape needs a *different*, simpler consumer to prove
itself while Tree-sitter is blocked. Cheapest candidate: the raw-brace
extraction lane the agent-task doc already assigns to CoreLexer, whose adapters
are new files by construction.

### Seam 3 — publish the lexical facts and give them a real consumer — **LANDED**

| Lane | Owner | Deliverable | Acceptance gate |
|---|---|---|---|
| Simple source lexical facts | CoreLexer | `simple_code_lines(source)` — per-line code with string CONTENT blanked and comments removed, columns preserved | 16/16 module spec; a no-op implementation must turn it red |
| First consumer | sspec_maintain | `_mask_strings_and_comment` deleted; `_is_pending` reads the shared fact | consumer suite equals its HEAD baseline example-for-example |
| String state | sspec_maintain | `in_triple_string` parity tracker deleted; replaced by `simple_string_continuation_lines` | new spec red against the old tracker, green after; corpus arm checked against an independent `it "` count |
| Docgen walkers | spipe_docgen | `in_docstring` per-line flag deleted from `extract_test_structure_with_default`; `parse_spipe_file`'s doc-block opener guarded by the same fact | new spec 6/6, **2/6 against the old walkers** (only the control and sabotage arm green); its three pre-existing baselines byte-identical (37/65, 5/5, 0-executed) |

**The docgen walkers were misreading 38 real files.** Both decided "am I in a
docstring?" from the current line alone, so a fixture string's bare closing
`"""` — 38 of the 70 spec files that open a fixture string close it that way —
put them INTO docstring mode on the way out. `extract_test_structure` then
dropped the next `describe` heading while rendering the fixture's interior as
real structure; `parse_spipe_file` collected the following code as a bogus doc
block and lost the real one after it, feature title included. Originally
deferred because the file sat in another lane's dirty set; that set was wiped
mid-session, which removed the reason.

**The parity tracker was losing 2,182 lines.** Replaying it over every
`*_spec.spl`: 32 files start a swallow at a comment line containing one triple
quote — worst `test/01_unit/test_runner/tag_parsing_spec.spl` at 181 of 182
lines, from line 1, so the scorer reported ZERO scenarios for a real spec.
This was deferred in the first pass as "a behavior change beyond this seam";
the measurement is what justified doing it. `cache_gc_quota`/`cache_gc_safety`
carry the construct but recover at the next triple quote — an earlier draft
named them as total losses, which was wrong.

`spipe_docgen/parser.spl` was the original candidate and is **deferred**: it is
in Codex's dirty set, so this lane cannot touch it. `sspec_maintain/source_facts.spl`
is clean, hand-rolls the same scanner, and became the consumer instead.

**What shipped**

`src/compiler/10.frontend/core/source_facts.spl` publishes what CoreLexer
already knows and every app-side scanner re-derives: for each line, which text
is code and which is merely inside a string or a comment. It is a lexical fact,
not a grammar — the lane's non-claim stands unchanged.

Two hand-rolled heuristics in `sspec_maintain/source_facts.spl` are provably
wrong on inputs the shared fact reads correctly, and both are pinned by
fixtures that run the legacy code and the shared fact over the same bytes:

| Heuristic | Input it gets wrong | Why |
|---|---|---|
| `_mask_strings_and_comment` | a docstring CONTINUATION line mentioning `skip(` | the line carries no quote of its own, so a per-line walk returns the prose verbatim and a downstream scan fires on it |
| `in_triple_string` (`count % 2`) | a triple quote written inside a COMMENT | the parity flips, the scanner enters docstring mode, and the rest of the file is discarded |

The question is not answerable one line at a time, which is why every
independent attempt at it has been wrong in the same way.

**What the consumer wiring bought, concretely.** An off-by-one in the module's
column padding — an exact-fit token treated as an overrun and given a separator,
rewriting `skip(` as `skip (` — passed the module's own 14 examples and was
caught within minutes of wiring a real consumer (`pending_detection_spec`
5/5 → 4/5). Fixed, with two regression examples. This is the practical case
against Seam 2's status quo: a foundation with no consumer has nothing pressing
on it.

**Now migrated.** The `in_triple_string` tracker is gone. The concern that
motivated deferring it — that changing it alters which lines reach fact
extraction — was addressed by preserving the `continue` structure exactly and
changing only the source of the boolean, so the set of skipped lines is the
same except where the parity count was wrong.

**Not re-entrant.** Both shared functions call `lex_init` and reset the global
CoreLexer. They are for tools that own their process; never for the compiler's
own parse path. That is a direct consequence of the 8 global-source sites
Seam 1 froze, and it disappears when Seam 1's debt is paid.

**Boundary that must stay.** Comments are DROPPED by the shared fact. Any
consumer whose fact lives in a comment (`# @req REQ-1`, `# @step: ...`) keeps
reading the raw line. Mixing the two is what made the hand-rolled scanners
ambiguous to begin with.

**Recommended remaining order: 1 → 2.** Seam 3 now supplies the pattern Seam 2
needs; `spipe_docgen` follows once Codex's lane unfreezes.

---

## Part 3 — What this lane shipped

- `scripts/check/check-parser-source-global-ratchet.shs` — fail-closed gate,
  `--selftest` fatal, verdict as last stdout line, baseline in
  `scripts/check/parser_source_global_baseline.txt` (8). Measured after the
  code change: `PASS — 16225 file(s) scanned, parser-source globals=8`.
- `src/compiler/10.frontend/core/source_facts.spl` — the shared lexical fact.
- `src/app/sspec_maintain/source_facts.spl` — first production consumer; the
  hand-rolled masker deleted.
- `test/01_unit/compiler/frontend/core_source_facts_spec.spl` (16 examples) and
  nine fixture files under `test/fixtures/source_facts/`.
- This document.

No file in Codex's dirty set was edited. `source_facts.spl` is clean at HEAD;
`core/source_facts.spl` is a new file beside dirty siblings, and it is imported
by module path so `core/__init__.spl` (dirty) needed no edit.

### Evidence

All runs on the aarch64 Rust **seed** at `bin/release/aarch64-unknown-linux-gnu/simple`
(154,560,904 bytes), copied into the worktree — the same binary `main` currently
uses. Findings therefore describe the seed, not a self-hosted compiler.

| spec | wired | HEAD baseline |
|---|---|---|
| `core_source_facts_spec.spl` | 21/21 | n/a (new) |
| `sspec_maintain/shared_lexer_string_state_spec.spl` | 6/6 | 3/6 against the old tracker |
| `sspec_maintain/pending_detection_spec.spl` | 5/5 | 5/5 |
| `sspec_maintain/scoring_spec.spl` | 18/20 | 18/20 |
| `sspec_maintain/rule_coverage_spec.spl` | 3/5 | 3/5 |
| `sspec_maintain/cache_spec.spl` | 6/6 | — |
| `sspec_maintain/report_multi_render_spec.spl` | 3/3 | — |

Four examples are red. All four are red at HEAD without this change, with
identical names; none is touched by this lane and none is hidden.

Sabotage (`simple_code_lines` replaced by a no-op passthrough), re-run against
the final spec: **21/21 green → 15/21 sabotaged → 21/21 reverted**. (An earlier
run of the same arm read 14/14 → 8/14, before five examples for the second
shared fact were added; the current numbers supersede it.)

Reproduce-first for the string-state fix: the consumer spec was run against the
OLD parity tracker first and went **3/6, with all three bug arms red**, then
6/6 with the fix.

**Docgen dependency cost**, same method: `spipe_docgen/main.spl` closure
**17 -> 22 files** (`lexer.spl`, `lexer_struct.spl`, `source_facts.spl`, and the
two `string_core` facades the lexer already pulls). Cycles unchanged.

**Dependency cost of the new `app -> compiler.frontend` edge, measured with
`bin/simple deps fast src/app/sspec_maintain/main.spl` at the pre-wiring
revision and after:** closure **91 -> 94 files**. The three are exactly
`core/lexer.spl`, `core/lexer_struct.spl`, `core/source_facts.spl` — the block
registry and the rest of the frontend are NOT dragged in. Cycles unchanged at 3,
all pre-existing in `std` (`io_runtime`/`process_ops`, `io`, `log`). The edge
itself is not new to the codebase: seven `src/app/**` files already import
`compiler.frontend`.

**`bin/simple lint` could not be run on the changed files, for pre-existing
reasons.** In this worktree it fails on *any* input, proven with a two-line
control file:

| mode | result on a 2-line trivial file |
|---|---|
| default (JIT) | abort, core dumped — `PANIC assertion failed: (diff >> 26 == -1) \|\| (diff >> 26 == 0)` at vendored `cranelift-jit/src/compiled_blob.rs:90`, an aarch64 ±128 MB branch-displacement overflow |
| `SIMPLE_EXECUTION_MODE=interpreter` | `error: semantic: class CodeLine has no field named code` — inside the linter's own `35.semantics/lint/lint_text.spl`, which is clean at HEAD |

Neither message mentions anything in this change (`CodeLine` appears in neither
changed file). The same trivial file lints exit 0 from the main checkout, so
this is a worktree/JIT-cache condition, not a defect in the new code — but it
means **no lint evidence exists for these files** and the claim is not made.

### Incidental finding — `spipe-docgen` does not run at the committed tip

The generated-manual mirror this lane owes (`bin/simple spipe-docgen <spec>
--output doc/06_spec --no-index`, `0 stubs`) **could not be produced**, and not
because of anything in this lane's spec. At `67859c96792`:

```
src/app/spipe_docgen/spipe_docgen/generator.spl:7
    use app.spipe_docgen.common.{..., spec_kw_line}
    -> error[E1002]: function `spec_kw_line` not found
```

`spec_kw_line` is defined at `common.spl:55` **only in Codex's uncommitted
working copy**; the committed `common.spl` does not contain it while the
committed `generator.spl` already imports it. Docgen fails identically on an
untouched pre-existing spec (`sspec_maintain/cache_spec.spl`), so this is not
specific to the new spec — it is an unlanded change sitting in the dirty set.

**Attempted and deliberately abandoned (2026-09-05).** This lane added the
5-line `spec_kw_line` helper to unbreak the tip. It resolved, and docgen then
failed on the NEXT missing symbol, `scenario_at_is_unconditional_pending`
(`parser.spl:1802`, also uncommitted). Measuring the real shape:

```
git diff --stat -- src/app/spipe_docgen/ src/app/sspec_maintain/analyzer.spl
    common.spl      |  5 +
    generator.spl   |  8 +-
    parser.spl      | 82 ++++++++++
    analyzer.spl    | 13 +-
    4 files changed, 105 insertions(+), 3 deletions(-)
```

The tip is not broken by one stray helper; it is missing a coherent ~105-line
feature across four files, three of which are dirty. Porting that wholesale
would mean committing another lane's entire in-progress change under this
lane's name, creating exactly the silent-divergence hazard that argues against
duplicating even one helper. **The addition was reverted.** The fix belongs to
the lane that owns the change; this document reports it so that lane, or the
next person to snapshot the tree, knows the tip does not build docgen.

Consequence for anyone reading a docgen result today: on a fresh clone the
command prints `OK <spec> (N lines)` and *then* errors, so a caller that reads
only the first line will record a success that produced no manual. The mirror
is owed once Codex lands `common.spl`; it is not waived.

## Handoff to the parser_framework merge owner (2026-09-05)

**Decision: this range is handed to Codex to land with its own work. It is not
pushed and will not be pushed by this lane.** Rationale: every file it touches
outside its own new files is owned by, or adjacent to, that lane's dirty set,
and landing it independently would race a merge owner who has to reconcile it
anyway.

**The range:** `69d13e0c097..a05eb9277fb`, 9 commits, on a linked worktree at
`/home/yoon/dev/simple-parser-sharing` (shared object store — the commits are
readable from `main` without fetching, e.g.
`git show a05eb9277fb:<path>`). The worktree HEAD is a gc root, so nothing is
collected while it exists; **do not `git worktree remove` it until the range is
landed or exported.**

**Landing base is contested — read before rebasing.** Measured 2026-09-05:

| ref | value |
|---|---|
| worktree base | `67859c96792` (main's tip at 15:10) |
| local `main` | `88c59bed70d` |
| local `origin/main` | `c8afd8a631c` — **stale**, never fetched to the real tip |
| remote `refs/heads/main` | `320e6d99e4b8b8540a65078f68ce8ffca15fd2b6` |

The machine additionally carries ~47 unpushed commits on the stale base. Use
`git ls-remote origin refs/heads/main` explicitly — this remote has 592 heads
and `ls-remote origin main` returns `refs/heads/archive/2026-09-03/main` first.

**Expected conflicts:** `config/check/must_check_gates.sdn` and
`scripts/check/check-push-must-pass.shs` (high-churn; one added row and one
added case arm, both adjacent to the `push-dual-run-shadow` rows). Everything
else in the range is either a new file or confined to
`src/app/sspec_maintain/source_facts.spl`, which is clean at HEAD.

**What must be re-verified after rebase**, since all evidence below was taken
on `67859c96792` with the aarch64 seed:

```sh
bin/simple test test/01_unit/compiler/frontend/core_source_facts_spec.spl          # 21/21
bin/simple test test/01_unit/app/sspec_maintain/shared_lexer_string_state_spec.spl #  6/6
bin/simple test test/01_unit/app/sspec_maintain/pending_detection_spec.spl         #  5/5
sh scripts/check/check-parser-source-global-ratchet.shs                            # PASS, globals=8
```

`scoring_spec` (18/20) and `rule_coverage_spec` (3/5) are red at HEAD too, with
identical example names — do not attribute them to this range.

**Two things this range deliberately leaves undone**, both belonging to the
merge owner: the ~105-line uncommitted `spipe_docgen` change that makes
`spipe-docgen` unrunnable from committed content
(`doc/08_tracking/bug/spipe_docgen_unrunnable_from_committed_content_2026-09-05.md`),
and therefore the `doc/06_spec` mirrors that change blocks.

## Explicit non-claims

- No claim of shared Simple **grammar**. The plan forbids it and this audit
  found no evidence for it.
- The ratchet proves a count did not grow. It does not prove any global is
  correctly scoped, nor that two parsers agree on source identity.
- Seam 3's byte-identical gate is a proposal; it has not been run.
- The audit greps production `src/` only. A boundary shared exclusively through
  test code is reported as test-only by design.
- The generated `doc/06_spec` manual for the new spec does not exist yet — see
  the docgen finding above. Its absence is recorded, not papered over.
- All evidence is from the aarch64 **Rust seed**, the binary `main` currently
  deploys. Nothing here is self-hosted-compiler evidence.
