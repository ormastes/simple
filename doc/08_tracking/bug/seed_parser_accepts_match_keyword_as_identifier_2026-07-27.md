# Seed parser accepts `match` keyword as an identifier — divergence detonates at bootstrap Stage 4
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** FIXED 2026-11-11 (lane p3-comp10) — seed parser now rejects the fatal class on the tracked seed; fix 68157645f47a in the deployed binary
**Found:** 2026-07-27 (Simple RISC-V hardening campaign, Lane H bootstrap redeploy)
**Area:** Rust seed parser (`src/compiler_rust/`) vs pure-Simple parser
**Severity:** medium — lets invalid code land, then fails the full-CLI stage of every bootstrap

## Finding

`val match = ...` (the `match` keyword used as a binding name) is **accepted by
the Rust seed parser** but **rejected by the self-hosted pure-Simple parser**
(`expected :, got Newline` — it commits to a `match <expr>:` expression).

Because Stages 2–3 compile only the `bootstrap_main` closure, the divergence is
invisible until Stage 4 parses the full tree with the freshly built self-hosted
compiler:

```
[parser_error] path src/std/nogc_sync_mut/compression/gzip/lz77.spl line 105:32: expected :, got Newline ''
[ERROR] phase 2 FAILED
```

Three stdlib files carried the pattern (all fixed by renaming to `matched` on
2026-07-27):

- `src/lib/nogc_sync_mut/compression/gzip/lz77.spl:104`
- `src/lib/nogc_sync_mut/compression/zlib.spl:79,157`
- `src/lib/common/compress/lzma2_encoder.spl:218,296,310`

## Which side is wrong

The self-hosted parser is correct: `match` is a language keyword. The seed's
leniency is the defect — it admits code the default toolchain cannot compile,
and the failure surfaces hours later in a different stage attributed to an
innocent file.

## Suggested fix

Reserve `match` (and audit other keywords) as identifiers in the seed parser so
seed-compiled code is a strict subset of self-hosted-compilable code. A cheap
interim guard: a lint/CI grep for `\b(val|var) match =` and keyword-binding
patterns.

## Interim guard (landed)

`scripts/check/check-keyword-identifier-bindings.shs` (run as
`sh scripts/check/check-keyword-identifier-bindings.shs`; exit 0 = clean, 1 =
violations as `file:line`) greps tracked `.spl` files under `src/` and `test/`
(vendored paths excluded) for keyword-as-identifier bindings. Fatal set:
`val match =` (the proven Stage-4 detonator class) and `val|var` bindings of
the hard keywords `if/else/for/while/return/fn/enum/struct/trait/use` in
`src/`. Deliberately not fatal, verified against both parsers on 2026-07-27 so
the gate is green on a healthy tree: `var match =` (grammar note G33 sanctions
it; spec-tested in `test/unit/core/parser_ce_keyword_identifier_spec.spl`),
`val class =` (accepted by both — no divergence), `val case =` (rejected by
both — the seed cannot land it). Warnings (non-blocking): the same binding
patterns in `test/` files (not part of the Stage-4 bootstrap tree; they fail
locally at test time — one live instance exists at
`test/03_system/tools/llm/claude_full/ink/screen_spec.spl:56`, left for its
owner) and function parameters named exactly `match` (one at
`src/lib/editor/services/md_search.spl:491`). Single grep pass, POSIX tools +
git only.

## Related

- Campaign plan: `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md` (Lane H)
- Same family (seed accepts / self-hosted rejects):
  `seed_parser_rejects_multiline_if_expression_chain_2026-07-27.md` (inverse direction)


## Triage 2026-11-11 (lane p3-comp10)

Verdict: FIXED (row's subject = the SEED accepting the fatal class). Fresh
re-verification at lane base 79d5af6723f6 against the tracked seed
bin/simple.exe (build 46fe8f6b6def, 2026-11-10):

- Direct probe of the row's exact claim: `fn main() -> i64: val match = 3;
  return match` now FAILS PARSE on the tracked seed with "reserved keyword
  'match' cannot be used as a val binding name" rc=1 (probe at
  build/review/comp10-probes/match_kw_binding.spl). The seed no longer admits
  the Stage-4 detonator class; seed-compiled code is back to a strict subset of
  self-hosted-compilable code for this shape.
- The guard message lives at
  src/compiler_rust/parser/src/stmt_parsing/var_decl.rs:58; its introducing
  commit 68157645f47a (2026-08-02, "fix: close claimed parser and byte
  marshalling bugs") IS an ancestor of both the lane base and the tracked seed
  binary. The doc's interim guard scripts/check/
  check-keyword-identifier-bindings.shs is present at tip (could not complete
  on this Windows host within 5 min — full-tree grep over tracked .spl files;
  not required for the verdict given the direct probe).
- Corpus spec test/01_unit/compiler/soft_keyword_identifier_corpus_spec.spl on
  the tracked seed: the match/case cases PASS, including "case -- the reported
  defect: match-arm marker only" and "un-reserving must not cost case its real
  job as a match-arm marker". 2 failures are an UNRELATED keyword-binding
  corner — `context/feature/scenario` and `lazy/skip/exists` bound as vals fail
  semantically with "type mismatch: cannot convert function to int"
  (soft_keyword_identifier_corpus_spec.spl:85,132). That is a different
  keyword-binding behavior question, recorded here as a residual observation;
  file separately if it matters.
- Evidence limit: test/01_unit/core/parser_ce_keyword_identifier_spec.spl (the
  doc's cited pin, path drifted from test/unit/core/...) is a PURE-SIMPLE
  parser pin — it imports core.ast/core.parser (parse_module, ast_reset, ...)
  and fails 6/6 on the tracked seed with "variable `par_state` not found"
  (the self-hosted parser API does not exist in the seed interpreter). It
  cannot serve as seed-side evidence; it will pin the self-hosted parser's
  matching behavior once a self-hosted binary is available.
