# Seed parser accepts `match` keyword as an identifier — divergence detonates at bootstrap Stage 4
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** FIXED (triage 2026-11-11, lane boot22; fix landed with PR #7597
`9e7e526edb` — verified ancestor of HEAD) — the seed parser's `parse_val` now
rejects `val match` bindings with `reserved keyword 'match' cannot be used as a
val binding name`; verified live on the tracked seed binary; zero fatal-class
instances in the tree; `var match` remains G33-sanctioned on both parsers.
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



## 2026-11-11 P3-boot22 triage — FIXED (header flip)

Row 7 of lane boot22 (bootstrap table, after #40). Re-verified FRESH at this
lane's base (`79d5af6723f6`, tracked seed build `46fe8f6b6def`):

- **Fix present in source.** `parse_val`
  (`src/compiler_rust/parser/src/stmt_parsing/var_decl.rs:51-62`) opens with an
  explicit `self.check(&TokenKind::Match)` rejection emitting exactly
  `reserved keyword 'match' cannot be used as a val binding name`, with an
  in-code comment citing the self-hosted divergence this record filed. It
  landed with PR #7597 (`9e7e7a526edb`), confirmed an ancestor of HEAD.
- **Verified live on the tracked seed binary.** Probe
  (`bin/simple.exe run` on `val match = 1; print(match)`): seed rejects with
  the reserved-keyword parse error — the Stage-4 detonator class can no longer
  be admitted by the seed. (The expression-context
  `TokenKind::Match => parse_keyword_identifier("match")` arm remains, but the
  val-binding path — the filed divergence — now rejects first.)
- **Tree census.** `git grep -E "(val|var) match *="` over src/ and test/:
  zero `val match =` instances; the surviving `var match = true` uses
  (e.g. `src/lib/blink/css_parser/selector.spl:95`) are the G33-sanctioned
  form both parsers accept — the self-hosted front end documents the same at
  `src/compiler/10.frontend/core/parser_stmts.spl:1022` ("G33: `match` may be
  an identifier"). The two parsers now agree on both forms.
- The interim grep guard (`scripts/check/check-keyword-identifier-bindings.shs`)
  remains in place as the cheap tripwire.

Residual: none for this row. A full Stage-1..4 bootstrap re-proof is the
standing bootstrap-lane grant, not part of this row's acceptance.
