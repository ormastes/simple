# Parser Sharing — Measured Audit and Next Shared Seam (contract v1)

**Date:** 2026-09-05 · **Status:** audit complete; Seam 1 and Seam 3 landed in this worktree, Seam 2 proposed
**Worktree:** `/home/yoon/dev/simple-parser-sharing` (detached `67859c96792`)
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

### Seam 3 — publish the code-vs-text fact and give it a real consumer — **LANDED**

| Lane | Owner | Deliverable | Acceptance gate |
|---|---|---|---|
| Simple source lexical facts | CoreLexer | `simple_code_lines(source)` — per-line code with string CONTENT blanked and comments removed, columns preserved | 16/16 module spec; a no-op implementation must turn it red |
| First consumer | sspec_maintain | `_mask_strings_and_comment` deleted; `_is_pending` reads the shared fact | consumer suite equals its HEAD baseline example-for-example |

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

**Explicitly NOT migrated.** The `in_triple_string` tracker in
`extract_sspec_source_facts` still runs. Replacing it changes which lines reach
fact extraction at all — docstring lines currently `continue` past everything,
including `# @req` scanning — and that is a behavior change beyond this seam.
It is the next reviewed step, not an oversight.

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
| `core_source_facts_spec.spl` | 16/16 | n/a (new) |
| `sspec_maintain/pending_detection_spec.spl` | 5/5 | 5/5 |
| `sspec_maintain/scoring_spec.spl` | 18/20 | 18/20 |
| `sspec_maintain/rule_coverage_spec.spl` | 3/5 | 3/5 |
| `sspec_maintain/cache_spec.spl` | 6/6 | — |
| `sspec_maintain/report_multi_render_spec.spl` | 3/3 | — |

Four examples are red. All four are red at HEAD without this change, with
identical names; none is touched by this lane and none is hidden.

Sabotage (`simple_code_lines` replaced by a no-op passthrough):
**14/14 green → 8/14 sabotaged → 14/14 reverted**, before the two later
regression examples were added.

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
specific to the new spec — it is an unlanded half sitting in the dirty set.

Consequence for anyone reading a docgen result today: on a fresh clone the
command prints `OK <spec> (N lines)` and *then* errors, so a caller that reads
only the first line will record a success that produced no manual. The mirror
is owed once Codex lands `common.spl`; it is not waived.

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
