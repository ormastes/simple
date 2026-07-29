# Bug/audit: two lexer position states coexist; three live mixing sites fixed, one whole cluster found fully dead

**Date:** 2026-07-29
**Status:** partially fixed (lane LEX1) — the three real MIXING sites found in
`_ParserDecls/fn_struct_decls.spl` (domain-block raw-brace parsing) now use
the live CoreLexer-backed accessors. The pre-existing legacy free-function
scanner cluster (`lexer_scanners.spl` + `lex_scan_token_local()` in
`lexer.spl`) was audited and found to be **fully dead code**, not merely
"legacy but self-consistent" as originally assumed — left in place with a
guard comment (deleting it requires updating two structural-existence specs,
out of scope for this lane).
**Found:** lane LEX1 (`lexer-position-unification`), mission-critical
robustness campaign, 2026-07-29
**Area:** compiler frontend (`src/compiler/10.frontend/core/`)
**Severity:** Medium — the three fixed sites gate real user-facing syntax
(`schema Name { ... }` / `style Name { ... }` / `ui Name { ... }` / `music`/
`bim`/`cad`/`city`/`rtl` domain blocks); the dead cluster is inert but was a
trap for future code to accidentally call.

## Background

SF2 (2026-07-27) found that `CoreLexer` (the struct-based lexer driving the
live parse path via `lex_next()` in `lexer.spl`) never writes its position
back into the legacy `lex_state_get/set("pos"|"line"|"col", ...)` slot (an
env-var-backed store used by a free-function lexer API that predates
`CoreLexer`). Code that mixes the two — reading the legacy slot from
CoreLexer-driven parsing — silently reads a permanently stale position. SF2
fixed two point instances (`unsafe:`/`danger:` block lookahead in
`parser_stmts.spl`, and the `asm { ... }` raw-brace scanner in
`_ParserPrimary/asm_raw_parsing.spl`) by introducing **live accessors**:
`lex_token_end_get()` (end offset of the current, already-lexed token),
`lex_live_line_get()`/`lex_live_col_get()` (current struct `line`/`col`), and
`lex_force_set_pos(pos, line, col)` (writes all three back into the live
CoreLexer struct so the next `lex_next()` resumes correctly).

This lane (LEX1) retires the hazard class: audit every caller of the legacy
accessors, classify each, and unify onto the live source.

## Caller classification table

| Site (file:line) | Accessor(s) used | Classification | Action |
|---|---|---|---|
| `parser_stmts.spl:511-520` (`unsafe:`/`danger:` block lookahead) | `lex_token_end_get()`, `lex_source_char_at()` | already live (SF2 fix) | none — verified as regression spec |
| `_ParserPrimary/asm_raw_parsing.spl:97-146` (`asm { ... }` raw-brace scan) | `lex_token_end_get()`, `lex_live_line_get()`, `lex_live_col_get()`, `lex_force_set_pos()` | already live (SF2 fix) | none — used as the reference pattern for this lane's fixes; verified as regression spec |
| `_ParserDecls/fn_struct_decls.spl:161-190` (`current_ident_is_cli_decl`, `cli Name:` lookahead) | `lex_token_end_get()` | already live (SF2 fix) | none |
| `_ParserDecls/fn_struct_decls.spl:136-145` (`current_ident_followed_by_lbrace`, domain-block `{` lookahead: `schema`/`style`/`ui`/`music`/`bim`/`cad`/`city`/`rtl`) | was `lex_pos_get()` | **MIXING** (dead legacy read in CoreLexer-driven parse) | fixed — switched to `lex_token_end_get()` |
| `_ParserDecls/fn_struct_decls.spl:192-215` (`parse_raw_domain_block_advance_lexer`) | was `lex_line_get()`/`lex_col_get()` (read) + `lex_pos_set()`/`lex_line_set()`/`lex_col_set()` (write) | **MIXING** (write-back silently discarded — CoreLexer's real position never advanced past the raw block body, so the next `lex_next()` would re-scan already-consumed content) | fixed — switched reads to `lex_live_line_get()`/`lex_live_col_get()`, write to `lex_force_set_pos()` |
| `_ParserDecls/fn_struct_decls.spl:222-226` (`parse_raw_domain_block_payload`, raw brace-depth content scan) | was `lex_pos_get()` | **MIXING** | fixed — switched to `lex_token_end_get()` |
| `lexer.spl:250-266` (`lex_pos_get/set`, `lex_line_get/set`, `lex_col_get/set` definitions) | wrap `lex_state_get/set(...)` | legacy definitions | left in place — still referenced by the dead cluster below; not deleted because it still has (dead) callers |
| `lexer.spl:569-606` (`lex_at_end`, `lex_peek`, `lex_peek_next`, `lex_peek_at`, `lex_advance`, `lex_match_char`) | `lex_pos_get/set`, `lex_line_get/set`, `lex_col_get/set` | **DEAD** — zero callers outside the equally-dead `lex_scan_token_local`/`lexer_scanners.spl` cluster below | left in place, guard comment added; see "Dead cluster" below |
| `lexer.spl:619-729` (`lex_scan_token_local`) | all of the above | **DEAD** — self-recursive only; zero external callers (confirmed by repo-wide grep) | guard comment added, not deleted (see below) |
| `lexer_scanners.spl` (`lex_scan_number`, `lex_scan_string`, `lex_scan_ident`, `lex_skip_spaces`, `lex_handle_indentation`, `lex_scan_token`) | same legacy accessors | **DEAD** — only external caller was `lex_scan_token_local`, itself dead | guard comment added at file top, not deleted |
| `_ParserDecls/fn_struct_decls.spl:688,695` inside `lex_scan_string`-era code — N/A, superseded | — | — | — |

(The table's "already live" rows were re-verified in this lane, not newly
discovered — they are SF2's fixes, re-confirmed correct and used as the
reference pattern / regression protection for the new fixes above.)

## Why the dead cluster was not deleted in this lane

`CoreLexer.next_token()` (a struct method in `lexer_struct.spl`, with its own
`scan_number`/`scan_string`/`scan_ident` methods operating on `self.pos`) is
the sole live tokenizer, reached via `lex_next()` in `lexer.spl`. The
free-function scanner path (`lex_scan_token()` in `lexer_scanners.spl`,
`lex_scan_token_local()` in `lexer.spl`, and the `lex_peek*`/`lex_advance`/
`lex_match_char`/`lex_at_end` primitives they use) is a **separate,
pre-CoreLexer scanning implementation that is no longer reachable from
anywhere** — confirmed by a repo-wide caller search (`grep -rn` for each
function name across `src/` and `test/`): `lex_scan_token_local` has zero
callers besides its own 4 self-recursive call sites, and nothing outside
`lexer_scanners.spl`/`lexer.spl` calls the 6 scanner functions.

Two specs assert the *text* of these functions exists
(`test/01_unit/compiler/lexer/lexer_spec.spl`,
`test/01_unit/compiler/lexer/lexer_comprehensive_spec.spl` — structural
`to_contain("fn lex_scan_number()")`-style checks, not behavioral), so
deleting the cluster requires touching those specs too. That is a distinct,
larger cleanup (~700 dead lines across 2 files + 2 spec updates) than this
lane's scope (position-duality fixes at live mixing sites). Recorded here as
a follow-up: **delete `lexer_scanners.spl`'s six functions, `lex_scan_token_local`
and its exclusive-use primitives (`lex_peek`, `lex_peek_next`, `lex_peek_at`,
`lex_advance`, `lex_match_char`, `lex_at_end`, `lex_make_token`,
`lex_make_simple`) and `lex_pos_get/set`, `lex_line_get/set`,
`lex_col_get/set`, `lex_state_get/set`, and update the two structural specs
to assert on the live `CoreLexer` API instead.**

## Regression protection

New spec: `test/01_unit/compiler/frontend/lexer_position_unification_spec.spl`
covers: (a) `unsafe:` block parses (SF2 regression), (b) `asm { nop }` scans
without "unterminated" and yields `EXPR_ASM` (SF2 regression), (c) a bare
`schema { ... }` domain block parses into the `__domain_block("schema", ...)`
marker call with the correct payload text (this lane's fix — previously
reading the dead legacy slot in
`current_ident_followed_by_lbrace`/`parse_raw_domain_block_payload`), and (d)
a nested-brace payload (`schema { inner: { x: i64 } }`) still finds the
matching close (guards the brace-depth scan against the position fix).
**Note on the domain-block grammar:** the parser-level dispatch
(`current_ident_followed_by_lbrace`) matches `<kind>{...}` / `<kind> {...}`
directly — there is no block-name token between the keyword and `{` (an
earlier draft of this spec incorrectly tried `schema Foo { ... }` and got a
plain `EXPR_IDENT` + `EXPR_STRUCT_LIT` instead, proving the dispatch simply
never fired for that shape). This matches
`frontend_domain_kind_for_line`/`frontend_may_have_domain_block` in
`10.frontend/frontend.spl`, the sibling line-based text-preprocessor that
handles domain blocks for the real `driver.spl` compile path (see "Two
domain-block implementations" below).

**Unrelated pre-existing landmine hit while writing (b):** embedding a bare
`{ ident }` span inside one ordinary double-quoted string literal in *this
outer* spec file trips Simple's own `{expr}` string interpolation — the
outer test-runner tries to evaluate `ident` as a variable and fails with
`semantic: variable 'ident' not found` (bare) or silently eats the escaped
quotes and fails the same way (`"{ \"ident\" }"`). `inline_asm_core_parser_spec.spl`
already fails 4/10 today for exactly this reason on its bare-mnemonic cases
(`cli`, `bkpt #0`, `fence rw, rw`, and the bare-`nop` warning-count case) —
run once during this audit at `Results: 10 total, 6 passed, 4 failed`. This
is pre-existing and unrelated to this lane's migration: the spec exercises
`_ParserPrimary/asm_raw_parsing.spl`, a file this lane did not modify (only
read, as the reference pattern for the fn_struct_decls.spl fixes). This
spec's (b) works around it with a raw string
(`r"{ nop }"`, no escape/interpolation processing — see
`lexer_struct.spl`'s `scan_raw_string`) for the brace-bearing segment.

## Two domain-block implementations (found during this audit)

`schema`/`style`/`ui`/`music`/`bim`/`cad`/`city`/`rtl` domain blocks are
handled by **two independent mechanisms**:

1. **Live, used by the real compiler:** `frontend_strip_domain_block_lines`
   (`10.frontend/frontend.spl`, called from `parse_full_frontend`, which
   `driver.spl` uses) finds whole lines matching `<kind>{...}` via plain
   string `starts_with`/`ends_with` *before* lexing/parsing even starts,
   collects them into `Module.domain_blocks`, and blanks the line so the
   parser never sees it. Single-line only, no lexer-position involvement at
   all (pure text scanning).
2. **Parser-level, reachable only via direct `parse_module` calls (unit
   tests, not the real driver path):** `enum_module_body.spl`'s
   `current_ident_followed_by_lbrace` dispatch to
   `parse_module_domain_block_decl`/`parse_raw_domain_block_payload` in
   `_ParserDecls/fn_struct_decls.spl` — the code this lane fixed. Multi-line
   capable (scans raw characters across newlines), but since
   `parse_full_frontend` always strips matching lines first, real source
   files compiled through `driver.spl` never reach this code — it only
   fires when something calls `core.parser.parse_module` directly on source
   that still contains `<kind>{`/`<kind> {` text (as the unit tests above,
   and this spec, do).

Not fixed or unified in this lane (out of scope — a distinct architectural
duplication, not a lexer-position bug): consider recording a follow-up to
either delete the parser-level implementation (if truly only test-reachable)
or wire the frontend-level stripper's block detection into a shared helper
so the two grammars can't drift further apart (the frontend one currently
requires zero space and single-line; the parser one tolerates whitespace and
spans lines).
