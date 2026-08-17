# Bootstrap parser quadratic source refetch

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Status

Parser scaling fixed; full bootstrap acceptance remains open. Blocks bounded pure-Simple bootstrap and therefore the imported-enum,
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
- A one-slice-per-token parser cache alone measured 12.459s/35.956s and did
  not satisfy the gate. The follow-up root audit found both interpreter
  function-block paths dropped `module_global[index] = value`: they only
  searched and updated the function-local environment. Both paths now preserve
  lexical-local precedence and fall back to updating `MODULE_GLOBALS`; focused
  global-persistence and local-shadowing oracles exit 0. Scaling must be
  measured once in the next bounded cycle.
- The approved post-root oracle measured 12.276s/27.631s (2.25x), so linearity
  remains acceptable but the 22 KiB absolute ceiling still fails. The
  493-source bootstrap was not launched.
- A current SharedText seed initially failed before the oracle because valid
  `self.field` syntax produced hundreds of false Python-mistake hints, then an
  unavailable monotonic-millisecond extern forced JIT/interpreter double load.
  Removing the invalid hint and using the exported microsecond clock made the
  oracle complete in 1.061s/4.172s. The 22 KiB absolute ceiling now passes;
  the 3.93x ratio and 968,524 KiB maximum RSS remain open.
- One equal-size discriminator parsed two 440-function modules with disjoint
  identifier vocabularies in 500ms/504ms. This rejects cumulative
  `core_token_text_intern` growth as the ratio owner; the cache stays.
  Static review also rejects bootstrap environment mirrors, duplicate-name
  scans, and native arena-array copying on this ordinary JIT path. The bounded
  three-cycle lane is exhausted. Next fresh cycle: time lexer-only 440/880
  inputs through public `lex_init`/`lex_next`/`TOK_EOF`; only then select a
  lexer or parser/AST fix.
- The fresh lexer-only probe measured 539ms/5,272ms and isolated the owner:
  `scan_ident` and `scan_number` each bound `self.source_chars` to a local
  array, so value-copy lowering cloned the entire source once per identifier
  or number token. Direct indexed field reads remove those copies without
  changing array semantics. The unchanged parser oracle now passes at
  33ms/75ms (2.27x), 205,192 KiB max RSS, and exit 0.
- A higher-requested, environment-gated mutable-object COW diagnostic was
  attempted three times against an isolated 22 KiB parse (exact generator and
  warm-up variants). Each SIGSEGVed before emitting a counter. All diagnostic
  code and fixtures were removed. COW remains a plausible but unproven owner;
  no aliasing-sensitive in-place rewrite was accepted.
- A subsequent Rust-only real-executor harness avoids the unstable parser
  runtime and deterministically proves the COW: executing
  `loaded = slot[0]; loaded.pos = 1; slot[0] = loaded` changes both field-map
  and source-buffer identity for 8-byte and 1 MiB sources while preserving
  values. The harness passes as a characterization test.
- A narrow indexed-place prototype was fully reverted before testing because
  the existing owned-self helper consumes fields but cannot return recoverable
  state on method error; correct rollback would otherwise require the same
  deep clone. Shared immutable `Value::Str` storage is the remaining reviewed
  semantics-safe owner, but its broad mechanical migration is not yet applied.
- The shared-text architecture is now higher-approved and implementation has
  started. Reproducible pre-migration RSS baselines are 200,292 KiB (parser)
  and 449,272 KiB (10,000 distinct retained short texts). The coherent type
  flip reduced compiler errors from 614 to 217 in three bounded cycles, then
  stopped at the mandatory cap. The migration remains incomplete and no parser
  scaling or bootstrap shard is authorized yet.
- Runtime slice offsets now follow lexer character indices, translating to
  UTF-8 byte boundaries in Rust and C. The prior byte-offset behavior was
  wrong for non-ASCII source; focused ownership/Unicode tests pass.
- The live parser now reads token text directly from `lex_cur_text_direct`;
  `parser_lex_source_cached()` and its environment generation counter had no
  callers. That obsolete cache, its generation update sites, and its two module
  slots were removed on 2026-07-25, confirming that the live parser no longer
  uses the original whole-source refetch mechanism. This does not yet satisfy
  the 22 KiB absolute-time gate.
- The available generation-1 pure-Simple candidate could not execute the
  scaling fixture: its HIR resolver reported exported `parse_module` and
  `parser_has_errors` unresolved. Both the implementation-path and canonical
  parser imports produced the same failure. The three-cycle cap stopped further
  retries, so no new timing receipt is claimed. Four stray consumers were
  normalized to the canonical `compiler.core.parser` spelling as source hygiene,
  not as a claimed fix.
- Read-only tracing isolated the unresolved imports to the CLI entry-closure
  BFS: it probed literal `src/compiler/core/...` paths and never reused the
  driver's numbered compiler resolver. The BFS now delegates `compiler.*`
  imports to that shared resolver and accepts the result only under a supplied
  source root. A fresh pure-Simple candidate is required before rerunning the
  exhausted timing fixture.

## Rejected fixes

- Mixed tuple lexer handoff, lexer-owned text slot, and direct scalar-text
  handoff all crashed the release-seed interpreted/JIT lexer path with SIGSEGV
  before producing token output. A separate minimal cross-module scalar/text/
  tuple probe passed, isolating the failure to lexer state transport rather
  than generic return ABI. All unproven lexer/parser edits were reverted.
- Parallel parsing is unsafe while lexer/parser state remains module-global.
- Existing pre-parse cache mode does not bypass `parse_all_impl()` and cannot
  accelerate the first cold build.
- The unused `SIMPLE_NATIVE_BUILD_SKIP_PRE_PARSE` prototype was removed on
  2026-07-25. It checked SHB freshness (and SMF freshness for combined output)
  but only checked native cache-record existence; it did not prove that native
  outputs existed or belonged to the exact backend/target/compiler/source
  scope, parser-confirmed facade/alias object set, and final link. It therefore
  could not safely authorize a link bypass.

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
