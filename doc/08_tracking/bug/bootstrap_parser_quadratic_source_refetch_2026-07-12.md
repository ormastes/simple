# Bootstrap parser quadratic source refetch

## Status

Partially fixed; absolute-performance acceptance remains open. Blocks bounded pure-Simple bootstrap and therefore the imported-enum,
UI/TUI, GUI, and WM runtime evidence gates.

## Evidence

- A profiled 493-source entry closure loaded in 320 ms.
- Phase-2 parsing then took 30-80 seconds for individual 11-26 KiB files;
  a 47 KiB file took about 194 seconds.
- `parser_lex_source_cached()` documents that its module cache slot does not
  persist under the interpreter, so token text falls back to refetching the
  whole `SIMPLE_BOOTSTRAP_LEX_SOURCE` value per token: O(file size squared).
- Interrupted builds persist no partial parser/object cache, so every bounded
  retry repeats the cold parse.
- A runtime-owned lexer-source cache removed the parser's whole-source clone
  from token-text reconstruction. The 11/22 KiB oracle now measures
  13.549s/28.380s (2.09x), proving near-linear scaling for that path, but still
  fails the 15s absolute ceiling. A second measurement was 14.766s/31.519s.
- Rust and C owners copy bounded UTF-8-aligned slices while holding their
  respective lock; returned text remains owned across source replacement.
- An attempted shared ASCII interpreter-slice fast path passed its focused
  unit test but did not improve the oracle, so it was removed rather than kept
  as speculative complexity. Host sampling is unavailable
  (`perf_event_paranoid=4`).

## Rejected fixes

- Mixed tuple lexer handoff, lexer-owned text slot, and direct scalar-text
  handoff all crashed the release-seed interpreted/JIT lexer path with SIGSEGV
  before producing token output. A separate minimal cross-module scalar/text/
  tuple probe passed, isolating the failure to lexer state transport rather
  than generic return ABI. All unproven lexer/parser edits were reverted.
- Parallel parsing is unsafe while lexer/parser state remains module-global.
- Existing pre-parse cache mode does not bypass `parse_all_impl()` and cannot
  accelerate the first cold build.

## Required fix and acceptance

Make lexer/parser state persist per parser invocation without whole-source
environment refetches or cross-call heap-text slots. Preserve exact token text
for structural, string, suffixed-number, error, and EOF tokens.

Acceptance requires:

1. `test/fixtures/parser_token_text_scaling/main.spl` exits 0, with the ~22 KiB
   parse under 15 seconds and no worse than 3x the ~11 KiB parse above the
   timing noise floor.
2. Exact token-text parity under the release-seed interpreted/JIT path.
3. The 493-source phase-2 parse completes within six minutes and the complete
   cached bootstrap shard within nine minutes, at no more than 1.5x RSS.
4. The newly built pure-Simple compiler passes the two-module imported-enum
   text oracle before UI evidence resumes.
