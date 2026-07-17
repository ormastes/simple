# Stage4 blocker: stage3 self-hosted parser fails multi-element case patterns the seed parses (2026-07-17)

**Found by:** release-sanity bootstrap chain, after stage1-3 went GREEN
(cranelift backend, `scripts/bootstrap/bootstrap-from-scratch.sh --backend=cranelift`
rc=0; stage2/stage3 produced, stage3 passed bootstrap compiler sanity).

## Symptom

Stage 4 (full CLI main.spl compile, using verified Stage 3) fails phase 2:

```
[parser_error] line 509:47: unexpected token in expression: : ':'
[parser_error_ctx] path src/compiler/mir_opt/mir_opt/collection_opt_core.spl kind 161 text ':'
(cascades at 513:39, 516:19)
```

First failing construct (`count_inst_uses` match):

```
case CallIndirect(_, ptr, args, _):
```

with cascade over the following `case Intrinsic(_, _, args):` and `case _:`.

## Isolation (A/B proven)

- Deployed Rust-seed binary (`bin/simple fix <file> --dry-run`): **0 parser
  errors** on BOTH the canonical `src/compiler/60.mir_opt/mir_opt/collection_opt_core.spl
  and the staged flattened copy `src/compiler/mir_opt/...` used by stage4.
- The failing region (lines 500-520) is byte-identical between the two copies —
  staging/flattening is NOT the corruption source.
- Therefore the defect is in the stage3 binary's parser: pure-Simple parser
  compiled via cranelift mis-parses a 4-element enum pattern with mixed
  binders/wildcards that the Rust seed parser accepts.

## Hypotheses (ranked)

1. **Cranelift miscompile of the parser's match/pattern code** — same class as
   the documented cranelift defects (enum `==` miscompile C5, byte-combine C6)
   in `simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md`.
2. Pure-Simple parser source genuinely lags the Rust parser on >3-element
   case patterns with trailing wildcard (parity gap) — less likely since the
   same source presumably parsed itself during stage2/3 sanity... unless the
   sanity subset avoids this construct.

Next probe: minimal .spl with a 4-element `case X(_, a, b, _):` fed to the
stage3 binary (`build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple`
native-build on a tiny source) vs the seed; then bisect binder/wildcard arity.

## Context

This is the LAST blocker in today's redeploy chain: stale-seed wall →
(fixed) seed spin → (fixed) f-string lexer regression ca58e1f →
(fixed/reverted) labeled-tuple io_runtime break → stage1-3 GREEN → THIS.
