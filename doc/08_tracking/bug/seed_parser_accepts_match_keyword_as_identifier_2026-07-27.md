# Seed parser accepts `match` keyword as an identifier — divergence detonates at bootstrap Stage 4

**Status:** open
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

## Related

- Campaign plan: `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md` (Lane H)
- Same family (seed accepts / self-hosted rejects):
  `seed_parser_rejects_multiline_if_expression_chain_2026-07-27.md` (inverse direction)
