# native_const_type_void_checked_join_host_facade_2026-11-07 (P1, open)

## Symptom
Stage3 `s3_fable57s` native-build of batch q0023 (s4e sweep) fails 20x with
`E-BACKEND-LLVM-CONST-TYPE: integer constant cannot define void` in
`lib.nogc_async_mut.sosix.host_facade` — `sosix_spawn_checked` (10) and
`sosix_run_bounded_checked` (10). Log: `C:/dev/p3new/s4/out/s4e_q/q0023/native-build.log.err`.

## Investigation (2026-11-07)
- Spec `test/01_unit/compiler/50.mir/native_const_type_void_checked_join_host_facade_spec.spl`
  lowers 10 reductions of both functions (typed `match` unwrap with `return Err(e)`,
  unit `?`, `?` on `Result<text?, E>`, `if val p = found: r = p` / `else: return Err|Ok(ctor)`,
  both full bodies with module-local helpers declared before and after) and counts
  Const/Copy defs into Unit-typed MIR locals (the #7329 harness metric).
- Result on origin/release/1.0.0 (seed-interpreted MIR lowering): **10/10 green, 0 void defs.**
  The shape does not reproduce in the MIR lowering logic at origin.
- The stage3 base `C:/dev/wt/p3-envpol2` (HEAD 25fede3cb71 + working-tree folds) does not
  contain `b961e59c064` (dominating if-result default def) or `28cd60b88ea` (#7329) as commits;
  its `lower_if`/`lower_if_chain` merge paths otherwise match origin for this shape.

## Root cause
Not yet located. Remaining hypotheses: (1) a stage3 native miscompile of the lowering itself
(the same source lowers cleanly when interpreted), or (2) a post-lowering MIR pass / backend
local-type view that the harness does not cover. Native MIR dump of host_facade from s3 is the
next step (blocked this session: C: had 2.4 GB free, below the 8 GB probe budget).

## Verification
Prevention spec green on origin (10/10). Native confirmation pending.
