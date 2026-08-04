# Stage 4 compiler-core `range` visibility

Status: claimed; root-cause repair in progress
Severity: P1 bootstrap blocker
Fix owner: `codex/stage4-x86-phase4` in `/home/ormastes/dev/pub/simple-stage4-x86-phase4`

## Exact failure

The first exact x86 Stage 4 run failed during HIR lowering of
`src/compiler/10.frontend/core/closure_analysis.spl` with `unresolved name:
range`. A local indexed-loop rewrite crossed that module in the second exact
run, which then failed in the adjacent compiler-core owner
`src/compiler/10.frontend/core/call_graph.spl` with the same diagnostic eight
times. This proves a shared bootstrap visibility defect rather than an invalid
loop in one feature.

Cycle 1 exited 1 after 59m50.82s at 21,946,576 KiB max RSS. Cycle 2 exited 1
after 1h10m20s at 22,105,500 KiB max RSS. No Stage 4 candidate exists and the
essential-tools and post-x86 gates remain blocked.

## Ownership and repair rule

`range` is valid Simple source and is used throughout compiler core. Repair its
pure-Simple bootstrap HIR/prelude visibility once; do not normalize every valid
loop into a manual `while`. The earlier `closure_analysis` rewrite is retained
only until the owner repair is verified, then should be reconsidered.

The first local edit preceded this formal record during continuation from an
already-running session; that ordering gap is recorded rather than hidden. The
adjacent `call_graph` reproducer is claimed here before its source is changed.

## Required evidence

1. Exact: the full x86 Stage 4 closure lowers both `closure_analysis.spl` and
   `call_graph.spl` without unresolved `range` diagnostics.
2. Adjacent: a focused bootstrap HIR fixture resolves `range` in two independent
   compiler-core modules, including multiple calls in one module.
3. Fail closed: unrelated unresolved names still stop HIR lowering.
4. The exact fresh CLI passes the bounded essential-tools smoke before any
   deployment or post-x86 platform execution.

## Retained logs

- `build/bootstrap-stage4-x86-phase4/logs/phase4-fresh-cycle1-20260804.stdout.log`
- `build/bootstrap-stage4-x86-phase4/logs/x86_64-unknown-linux-gnu/stage4-native-build-cycle1-20260804.log`
- `build/bootstrap-stage4-x86-phase4/logs/phase4-fresh-cycle2-20260804.stdout.log`
- `build/bootstrap-stage4-x86-phase4/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`
