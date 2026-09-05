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
| `source_facts_line_count(source) -> i64` | line count; both arrays index beside `source.split("\n")` |

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
- Specs: `test/01_unit/compiler/frontend/core_source_facts_spec.spl` (21),
  `test/01_unit/app/sspec_maintain/shared_lexer_string_state_spec.spl` (6),
  `test/01_unit/app/spipe_docgen/shared_lexer_string_state_spec.spl` (6)
- Fixtures: `test/fixtures/source_facts/` (11)

## Known open

- `spipe-docgen` does not run from committed content at all — the committed
  generator/parser/analyzer reference a ~105-line change that is still uncommitted
  across four files. So no `doc/06_spec` mirror exists for the specs above, and none
  can be generated until that lane lands. Do not hand-write one.
- `src/app/spipe_docgen/spipe_docgen/parser.spl` now consumes both facts for its two
  docstring walkers (`parse_spipe_file` doc-block collection and
  `extract_test_structure_with_default`). Its remaining ~250 text-scan sites are
  per-line *grammar* recognition (`describe `, `it `, `step(`), not string state —
  leave them. `find_scenario_body_end` is still indent-only and not string-aware; a
  fixture's column-0 lines end a scenario body early. Measure before migrating.
