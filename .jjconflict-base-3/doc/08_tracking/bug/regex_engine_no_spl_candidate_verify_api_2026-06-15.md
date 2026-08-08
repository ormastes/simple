# Bug: regex engines expose no importable `.spl` candidate-verify API

- id: regex_engine_no_spl_candidate_verify_api_2026-06-15
- date: 2026-06-15
- severity: P3 (lib friction / blocked integration)
- area: lib/common/regex_engine, lib/common/regex, lib/common/search
- status: open

## Summary
The Phase-1 search prefilter (`src/lib/common/search/prefilter.spl`, AC-4) is
meant to feed its candidate window set to the existing regex engine for the
final verify step (`prefilter -> candidate -> verify -> result`). Neither
directory-level engine is cleanly callable from Simple source:

- `src/lib/common/regex_engine/` contains ONLY compiled `.smf` artifacts
  (`matcher.smf`, `dfa.smf`, `nfa.smf`, `parser.smf`, ...). There is no
  `*.spl` source in that directory to `use` and no documented stable entry
  point for "does this candidate substring match this compiled pattern".
- `src/lib/common/regex/` is likewise `.smf`-only (`match.smf`, `parse.smf`, ...).

There is no exported function with a signature like
`fn verify_at(pattern, haystack_bytes, start) -> bool` or
`fn is_match(pattern, candidate) -> bool` reachable from a `.spl` consumer in
`src/lib/common/search/`.

## Impact
The prefilter could not call the real regex engine for verification. For the
literal/trigram path this phase covers, the correct verify is an exact
byte-equality check at the candidate offset, so `prefilter.spl` verifies via
`Haystack.matches_at(cand, Pattern)` instead. This is correct for literal /
mandatory-literal-factor patterns (the only ones a literal/trigram prefilter
screens) but means a true *regex* factor cannot yet be re-verified through this
pipeline.

## Repro
1. From `src/lib/common/search/prefilter.spl`, attempt
   `use std.common.regex_engine.matcher.{...}`.
2. No `.spl` source exists for that module; the package ships `.smf` only.

## Requested fix / feature
Expose a small importable `.spl` candidate-verify surface from the regex engine,
e.g. `regex_engine/verify.spl` with:
- `fn compile(pattern_src: text) -> CompiledRegex` (or reuse existing)
- `fn matches_at(re: CompiledRegex, hay: [u8], start: i64) -> bool`
- `fn is_match(re: CompiledRegex, candidate: [u8]) -> bool`

so the search prefilter can hand candidate windows to the engine for the verify
step. Track as a feature request alongside this bug.

## Related
- AC-4 of `.spipe/search-custom-types/state.md`
- `doc/03_plan/lib/search/custom_type_alpha_search_team_plan_2026-06-15.md`
