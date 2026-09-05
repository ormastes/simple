# Parser Sharing — Measured Audit and Next Shared Seam (contract v1)

**Date:** 2026-09-05 · **Status:** audit complete, seam proposed, no code landed
**Worktree:** `/home/yoon/dev/simple-parser-sharing` (detached `67859c96792`)
**Audited state:** the `main` working copy at `/home/yoon/dev/simple` on
2026-09-05, *including* Codex's 38 uncommitted modified files and its untracked
`structural_adapter/`, `lexer_tape.spl`, `canonical_adapter.spl` work. The
worktree is at the committed tip and therefore does **not** contain that work;
it exists so this lane can add files without touching Codex's dirty set.

**Lane etiquette.** `doc/03_plan/agent_tasks/parser_framework.md` freezes the
merge contract and forbids editing another lane's dirty files. Every parser file
this audit names is in Codex's dirty set. This document therefore proposes; it
does not edit. The merge owner (Codex) and final reviewer (Astra) decide
adoption.

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

### Seam 3 — bring `spipe_docgen` inside the sharing perimeter

| Lane | Owner | Deliverable | Acceptance gate |
|---|---|---|---|
| Docgen source facts | spipe_docgen | `parse_spipe_file` obtains indentation, docstring and declaration boundaries from a shared lexical result rather than per-line text scans | docgen output byte-identical on the existing corpus before/after; no new grammar claim |

Scoped deliberately narrow. `spipe_docgen` needs *lexical* facts — indent
depth, docstring extent, string literal boundaries — not a grammar. That is
exactly what the CoreLexer tape publishes, which makes docgen a better first
tape consumer than Tree-sitter: it has an existing byte-comparable output
oracle (generated manuals) and no interpreter method-dispatch blocker.

**Recommended order: 1 → 3 → 2.** Seam 3 supplies the consumer that Seam 2
needs, and unlike Tree-sitter it is not blocked on
`doc/08_tracking/bug/treesitter_interpreter_method_dispatch_2026-09-05.md`.

---

## Part 3 — What this lane shipped

- `scripts/check/check-parser-source-global-ratchet.shs` — fail-closed gate,
  `--selftest` fatal, verdict as last stdout line, baseline in
  `scripts/check/parser_source_global_baseline.txt` (8).
- This document.

Nothing else. No `.spl` file was touched: every one that matters is in another
lane's dirty set.

## Explicit non-claims

- No claim of shared Simple **grammar**. The plan forbids it and this audit
  found no evidence for it.
- The ratchet proves a count did not grow. It does not prove any global is
  correctly scoped, nor that two parsers agree on source identity.
- Seam 3's byte-identical gate is a proposal; it has not been run.
- The audit greps production `src/` only. A boundary shared exclusively through
  test code is reported as test-only by design.
