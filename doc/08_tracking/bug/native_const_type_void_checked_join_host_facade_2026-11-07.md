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

## Additional reproduction (2026-11-07, run-15 Stage 2 on aarch64)
The bootstrap run-15 Stage 2 binary
(`/home/yoon/dev/simple-bootstrap/build/bootstrap-opus-15/stage2/aarch64-unknown-linux-gnu/simple`,
`SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1 native-build`) fails the same way on a non-generic
four-line function, so the shape is not specific to `host_facade`:

```simple
fn plain_flag(xs: [i64]) -> bool:
    var found = false
    for i in 0..xs.len():
        if xs[i] == 2:
            found = true
    found
```

`E-BACKEND-LLVM-CONST-TYPE: integer constant cannot define void ... function=...plain_flag`.
Every probe with an else-less assigning `if` inside a loop body hit it (3 of 3); a
loop-free probe in the same file compiled.
This supports hypothesis (1): the seed-built Stage 2 miscompiles the lowering of an
else-less `if` statement. It also blocks native runtime verification of any
Stage-2-built probe that uses that shape (found while verifying the erased generic
`==`/`.hash()` lowering for adaptive_map/map/hash).

## Native reproducer from run-15 Stage 2 (2026-11-07)

A single-file user program reproduces the backend error on the frozen run-15
Stage 2 binary (`/home/yoon/dev/simple-bootstrap/build/bootstrap-opus-15/stage2/aarch64-unknown-linux-gnu/simple`,
`SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1 <stage2> native-build main.spl`):

```simple
struct M:
    matched: bool
    count: i64

fn m1(n: i64) -> Option<M>:
    if n > 100: return None
    Some(M(matched: n > 1, count: n))
```

`compile error: E-BACKEND-LLVM-CONST-TYPE: integer constant cannot define void;
use an explicit MIR Cast for numeric conversion [module=main function=main.m1]`.
Shape: an early `return <Enum value>` followed by a final enum value. Writing
the body as `if n > 100: None else: Some(M(..))` compiles and runs (verified
with a Stage 2 built from work/optional-record-some-literal-owner-20261107), so the trigger is the early-return + tail combination, not the
Option record itself.

Run-15 compiler closure: `grep -rl -e "cannot define void" -e CONST-TYPE`
over `bootstrap-opus-15/logs`, `stage2-compiler-tests/` and `stage3/` finds no
hit. That is NOT evidence the closure is clean: the `compiler_cli_build` row
stopped at `[mir-shard] outcome=fail ... link and artifact publication
blocked` (2298 failed modules), so backend codegen never ran for the closure.
Because the shape is common in compiler sources, expect it to surface once
MIR admission passes; the Stage 3 host_facade failure above may be the same
defect.
