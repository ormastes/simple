# Feature Expert — Parser Infrastructure Sharing

## Role

Own process knowledge for **sharing Simple-source parser infrastructure** — stopping
tools outside the compiler from re-deriving, by hand, facts CoreLexer already knows.

This is NOT the `parser_framework` lane. That lane (merge owner Codex, reviewer Astra,
`doc/03_plan/agent_tasks/parser_framework.md`) owns the generic multi-dialect
`ParseDialect`/`ParseRuntime` runtime and the Simple dialect. This one covers the
narrower, adjacent question the framework's acceptance gates cannot see: app-side
scanners under `src/app/**` that parse Simple source with `trim`/`starts_with`/
`contains`, outside every owned path in the frozen matrix.

If you are about to hand-roll "is this text code or is it inside a string/comment?",
stop — that fact is published. See below.

## The shared facts

`src/compiler/10.frontend/core/source_facts.spl`:

| Function | Answers |
|---|---|
| `simple_code_lines(source) -> [text]` | per line, the CODE only: string literal CONTENT blanked, comments removed, columns preserved by pad-to-column |
| `simple_string_continuation_lines(source) -> [bool]` | per line, is this a continuation of a string opened on an earlier line |
| `simple_string_byte_ranges(source) -> [[i64]]` | per line, the BYTE ranges (line-relative, `[s0,e0,s1,e1,…]`) inside string tokens — for byte-scanning tools that must keep byte columns |
| `source_facts_line_count(source) -> i64` | line count; all arrays index beside `source.split("\n")` |

**NOT re-entrant.** Both call `lex_init`, resetting the global CoreLexer. Safe for a
tool that owns its process; never call from inside an in-progress parse. This follows
directly from the 8 remaining `current_core_source_*` sites, frozen by
`scripts/check/check-parser-source-global-ratchet.shs`.

**Comments are dropped.** A fact that lives in a comment (`# @req REQ-1`,
`# @step: ...`) must still be read from the raw line. Mixing the two is what made the
hand-rolled scanners ambiguous to begin with.

## Why: the two defects this closes

Both were live in `src/app/sspec_maintain/source_facts.spl`, both measured 2026-09-05.

1. **Per-line string masking cannot see a docstring.** A `_mask_strings_and_comment`
   character walk returns a docstring's CONTINUATION line verbatim — the line carries
   no quote of its own — so a scan for `skip(` fires on prose. Patched twice upstream
   before being deleted.
2. **A triple-quote parity count is not string state**, and neither is a
   one-line-at-a-time docstring flag. spipe_docgen's two walkers could not tell a
   docstring's bare closing `"""` from a FIXTURE string's (`val src = """ ... """`),
   so they entered docstring mode on the way OUT of a fixture. **70 spec files open
   a fixture string; 38 close it with a bare `"""`** — the exact trigger.
   Also: `count('"""') % 2 == 1` is
   right only for well-formed docstrings. One triple quote in a COMMENT flips it and
   discards every line until the next triple quote. **Replaying the legacy tracker
   over every `*_spec.spl`: 32 files affected, 2,182 lines discarded** — worst
   `test/01_unit/test_runner/tag_parsing_spec.spl` at 181 of 182 lines, from line 1,
   so the scorer reported ZERO scenarios for a real spec.

The general lesson: **the question is not answerable one line at a time**, which is why
every independent attempt got it wrong the same way.

## Traps

- **A shared artifact with zero production consumers is test-only, not "landed."**
  Two rows in the `parser_framework` matrix claimed "landed" with no importer. Wiring
  a real consumer here found an off-by-one within minutes that the module's own 14
  examples had passed: an exact-column-fit token was treated as an overrun and given a
  separator, rewriting `skip(` as `skip (`.
- **Error tokens (kind 191) carry a diagnostic in `.text`**, e.g. `unexpected
  character: 안`. Emitting it injects words the source never contained. Drop them.
- **Do not commit a CRLF fixture** — git normalizes it on checkout and the example goes
  vacuous everywhere but the authoring machine. Build CRLF in the spec and assert the
  source really contains `\r\n`.
- **`bin/simple run` and `bin/simple test` diverge.** `extract_sspec_source_facts` dies
  with `Function 'str.split' not found` under `run` while passing under `test`. Put
  corpus assertions in specs.
- **Compare against an independent oracle, not the extractor's own output.** The corpus
  arm counts `it "` openers separately and requires the extractor to match.

## Feature Links

- Audit + design: `doc/05_design/platform/structural_compute/parser_sharing_contract_v1.md`
- Adjacent lane (do not edit its dirty files): `doc/03_plan/agent_tasks/parser_framework.md`,
  `doc/03_plan/platform/structural_compute/parser_framework_plan.md`
- Gate: `scripts/check/check-parser-source-global-ratchet.shs` (+ baseline; push-tier, advisory)
- Specs: `test/01_unit/compiler/frontend/core_source_facts_spec.spl` (28),
  `test/01_unit/app/cli/query_source_mask_shared_lexer_spec.spl` (11),
  `test/01_unit/app/check/check_sspec_guidance_shared_lexer_spec.spl` (7),
  `test/01_unit/app/sspec_maintain/shared_lexer_string_state_spec.spl` (6),
  `test/01_unit/app/spipe_docgen/shared_lexer_string_state_spec.spl` (12)
- Fixtures: `test/fixtures/source_facts/` (17)
- Backlog (measured, classified): design doc § "Measured backlog" — 27 Simple-source
  trackers remain; the `35.semantics/lint` family is BLOCKED by the 8 global-lexer
  sites (re-entrancy), not merely deferred.

## Seams 6-8 (2026-09-06)

| tool | tracker removed | defect | corpus |
|---|---|---|---|
| `app/check/concurrency_lint.spl` | whole-source char walker | a `'…'` string holding `"""` left it believing a string was open; the next line's deprecated import was masked away and its E-PAR-002 never fired. It also blanked the OPENING quote, so two E-PAR-004 string-argument checks could never match — dead at HEAD, probed at 0 diagnostics | 7 src files |
| `test_runner` preprocess x3 (`test_result_wrapper`, `test_runner_execute` lib + app copies) | `in_docstring` toggled by any `"""`-prefixed line | a ONE-LINE docstring toggled it on and nothing toggled it off; every later import and top-level declaration was pushed, indented, into `fn main()` | 1,657 spec files |
| `90.tools/verify/aorte_obligation_census_scan.spl` | per-line `"""` parity count | ran on the raw line BEFORE the comment check, so a comment mentioning the delimiter dropped the next obligation site from the certification census | 45 src files |

**Measured and NOT migrated** — `backend_plugin_boundary_scan.spl`: the defect
shape is real (a docstring continuation line has no quote, so its prose is
scanned as code), but a corpus replay found **0** files where a continuation
line carries a provider call. No discriminating input in the tree ⇒ no
migration. Also rejected: `query_diagnostics`, `svim/lsp_features`,
`ui_test/parse`, `jupyter_kernel`, `mcp/main_lazy_json` (all JSON),
`verify/checker.spl` (Lean), `builtin_blocks_shell` (shell) — other grammars,
must never call CoreLexer. `mode_filter` re-confirmed harmless. Fragment-level
matchers (`spipe_matching_close_paren`, `easy_fix/rules_helpers`) take a
substring with no line context — signature mismatch, not migratable as-is.

**Threading note:** the preprocess loop became `while line_index < lines.len()`
with the index advanced at the TOP, so every one of its ~10 `continue` paths
stays correct. A `for … in` loop cannot carry the fact index.

## Known open

- `spipe-docgen` does not run from committed content at all — the committed
  generator/parser/analyzer reference a ~105-line change that is still uncommitted
  across four files. So no `doc/06_spec` mirror exists for the specs above, and none
  can be generated until that lane lands. Do not hand-write one.
- `src/app/spipe_docgen/spipe_docgen/parser.spl` now consumes both facts for its two
  docstring walkers (`parse_spipe_file` doc-block collection and
  `extract_test_structure_with_default`). Its remaining ~250 text-scan sites are
  per-line *grammar* recognition (`describe `, `it `, `step(`), not string state —
  leave them. `find_scenario_body_end` now takes the continuation fact as a parameter
  (threaded through its 7-function chain rather than a module global) and never
  ends a body on a line inside a string — 11 spec files had bodies cut at a
  fixture's column-0 interior.
- `src/app/cli/query_source_mask.spl` (four `query`/`check` consumers) and
  `check_tier.spl` now take string detection from `simple_string_byte_ranges` and
  keep their **byte** columns — consumers hand those columns to byte-indexed
  helpers over the raw line, so a char-column drop-in would have corrupted them.
  That is why the third fact exists. `strip_strings_and_comments` is gone.
