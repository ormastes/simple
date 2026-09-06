# `query_source_mask` cannot see single-quoted strings — `'"""'` swallows the file

## Status

**Resolved in PR #373** (branch `parser-sharing-2026-09-05`), by a design that
did not need the column decision this record first asked for: the scanners
keep their byte columns and take only the string byte ranges from the lexer
(`simple_string_byte_ranges`). The measurement and the reasoning below are
kept as the record of why a character-column drop-in was wrong.

## Symptom

`src/app/cli/query_source_mask.spl` masks strings and comments for the
`simple query` / `simple check` lint scanners (`check_tier.spl`,
`query_lint.spl`, `query_check.spl`, `query_lint_checks.spl`). Its two scanners
— per-line `strip_strings_and_comments` and cross-line
`_first_code_pattern_projection` — recognise only double-quoted strings
(byte 34). Neither handles a single-quoted `'…'` string, which CoreLexer lexes
as an ordinary `StringLit` (kind 3; measured 2026-09-05 with a direct probe:
`val s = '# not a comment'` → one token, text `# not a comment`).

Two consequences, both in code the scanners are pointed at:

| source shape | scanner behaviour |
|---|---|
| `if trimmed[0] == '#':` | `#` inside the string is read as a comment start; the rest of the line is dropped from pattern scanning |
| `if trimmed.starts_with('"""'):` | the `"""` inside the string flips `in_triple_string`; **every following line until the next `"""` in the file** is skipped for `return`/safety-pattern/dunder scanning (the walker recovers at the next triple quote, so the damage is a window, not the whole file — an earlier draft of this record overstated it) |

## Measured over `src/**/*.spl` (vendor excluded), 2026-09-05

**20 files** contain a single-quoted string holding `#` or `"""` on a
non-comment line. Two are the window-swallowing shape, and both are in the
compiler's own tooling:

```
src/compiler/90.tools/verify/aorte_obligation_census_scan.spl:246   if trimmed.starts_with('"""'):
src/compiler/90.tools/verify/flight_rule_census_scan.spl:292        ... .starts_with('"""'):
src/compiler/10.frontend/parser/partial.spl:169                     ... trimmed[0] == '#':
src/compiler/10.frontend/treesitter/heuristic.spl:111               ... trimmed[0] == '#'):
```

So `simple query`/`check` lint results for those files are silently partial
over the swallowed window.

## Why this is not a drop-in migration

The shared fact `simple_code_lines` (`src/compiler/10.frontend/core/source_facts.spl`)
answers exactly this question and handles `'…'` correctly. But:

1. **Column semantics differ.** `_first_code_pattern_projection` reports
   `column = byte_offset + 1` on the ORIGINAL line. `simple_code_lines`
   preserves the lexer's CHAR column. They agree on ASCII and disagree on any
   line with a multibyte character before the match. Whether consumers want
   byte or char columns (LSP-style positions are usually char-based) has to be
   decided, and the existing behaviour may itself be the bug.
2. **`check_tier.spl:285` masks an already-trimmed single line**
   (`strip_strings_and_comments(trimmed)`), while the shared fact is
   whole-source. That call site needs the whole file threaded to it — a
   signature change in a consumer this lane does not own.

## Resolution (as landed)

Byte columns were the right contract and were kept. A third shared fact,
`simple_string_byte_ranges(source) -> [[i64]]`, gives per-line byte ranges of
string payload; the three scanners skip those bytes and stop at the first `#`
outside them. `check_tier` computes `simple_code_lines`/
`simple_string_continuation_lines` once per file. Spec:
`test/01_unit/app/cli/query_source_mask_shared_lexer_spec.spl`.

## Related

- `doc/05_design/platform/structural_compute/parser_sharing_contract_v1.md`
- `doc/00_llm_process/feature_expert/parser_sharing/skill.md`
