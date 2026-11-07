# native_const_type_void_checked_join_host_facade_2026-11-07 (P1, open -- root cause fixed; host_facade Stage 3 re-run pending)

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

## Root cause (2026-11-07, located with a traced Stage 2)

`src/compiler/50.mir/mir_lowering_stmts.spl` `lower_if_chain` bound
`val chain_has_else = else_.?`. `.?` returns the `HirBlock?` itself, not a
bool (syntax reference: "Existence Check (`.?`) -- Returns `T?`"). The
`if chain_has_else:` result-type test treats the absent Option as false (the
result temp is Unit), but the dominating-default guard
`if chain_has_else and expected_type == nil:` (added by `b961e59c064`) read the
absent Option's raw nil-sentinel word as true in the seed-compiled Stage 2. So
every else-less `if` -- every `if c: return X` and every assigning
`if` with no `else` -- got `Const 0` into its Unit result, and LLVM codegen
rejected it ("integer constant cannot define void"). The seed-interpreted
lowering evaluates the `and` by truthiness and stays clean, which is why the
interpreted harnesses were green at both run-15's source (`dba24b97b4d`) and
origin. `0ba2d79b542` (payloadless merge guard) did not help: the bad def is
emitted at chain entry, not at the merge.

Trace evidence (temporary probes, not committed), Stage 2 from origin
`60f2b2c9dfe` on `fn ret1(c: bool) -> i64: if c: return 1 / 0`:
`[zz-emit] UNIT-DEST dest=2 v=0` emitted before
`[zz-ifjoin] site=chain-entry che=nil result=2 ... exp_nil=true`, then
`E-BACKEND-LLVM-CONST-TYPE ... zzdest=2`.

## Fix
`val chain_has_else: bool = else_ != nil` (a real bool). It also fixes the
same misread at the arm-copy guard `chain_has_else and not local_is_unit(..)`.
No other untyped `val x = y.?` binding exists in `50.mir` / `70.backend`; the
typed `val x: bool = y.?` sites in
`_MirLoweringExpr/switch_operators_calls.spl` (~4947-4955, the
`SIMPLE_ENUM_PAYLOAD_PATH_TRACE` diagnostic, incl. `effective_present` driving
its printed `route`) are trace-only and listed under the follow-up below.

## Native red/green (aarch64, `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1 native-build`)
- Red: frozen run-15 Stage 2 and a Stage 2 built from unmodified origin
  `60f2b2c9dfe` both fail `full.spl` (plain_flag, ret1, ret_text, pick, elif
  chain without else) and `opt.spl` (`if n > 100: return None` then
  `Some(M(..))`) with E-BACKEND-LLVM-CONST-TYPE.
- Green: Stage 2 built from the fix (seed `seed-try-target/release/simple`,
  run-15 Stage 2 argv, `--threads 6`, 16G scope, 1617 compiled, 0 failed)
  builds and runs them: `full` prints `true false 1 0 a b 1 0 10 20 0`,
  `opt` prints `5 -1`; if/else shapes still print `1`.
- Spec: `test/01_unit/compiler/mir/else_less_if_unit_merge_const_spec.spl`
  (the reported shapes, with and without Unit attribution). It is green
  interpreted before and after the fix: the defect needs the native lane, so
  the native rebuild above is the gate.

## Follow-up observed (not fixed here)
`fn g(b: B?) -> bool: val h = b.?; h` returns `true` for `nil` both
interpreted and native: a `T?` flows into a `bool` return with no presence
conversion. Same `.?`-as-bool class; separate from this fix. The trace-only
`val x: bool = y.?` bindings in `switch_operators_calls.spl` (~4947-4955) are
in the same class.
