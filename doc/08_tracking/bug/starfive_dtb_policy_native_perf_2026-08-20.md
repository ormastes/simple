# StarFive DTB policy native performance exceeds the C parity budget

Status: source fix verified with bootstrap seed; pure-Simple acceptance deferred

## Reproducer

- C oracle: `test/02_integration/os/kernel/arch/riscv64/starfive_dtb_policy_oracle.c`
- Simple benchmark: `test/05_perf/hal/starfive_dtb_policy_perf.spl`
- Compiler: current Rust bootstrap seed, native aggressive optimization
- Workload: 50,000,000 identical scalar selection decisions; checksums must match
- Samples are warm wall-clock seconds; median of five.

## Observed

The third and final optimization cycle measured C `0.09s` and Simple `0.30s`,
or `3.33x`. The required ceiling is `3.0x`. Checksums were identical at
`34089754400000000`.

Changing the exported policy ABI from mixed `u64/u32/u32` scalars to uniform
`u64/u64/u64` improved the ratio from `3.38x` to `3.33x`, but did not close the
gap. The optimizer reports only two low-confidence dead-code-elimination
opportunities and no algorithmic or allocation issue in the policy owner.

## Suspected owner

The remaining gap is in native scalar call/branch lowering for an exported
cross-language function, not DTB selection complexity. Investigate inlining or
specialization of locally called `@export("C")` functions while retaining the
external symbol, boolean-to-integer lowering, and branch layout.

## Source fix and diagnostic evidence

Coverage recording now uses an explicit `starfive_dtb_policy_select_coverage`
entry point over the same pure decision core. The production
`starfive_dtb_policy_select` ABI no longer performs coverage-mode global checks
or writes. This keeps test instrumentation out of the deployed C-to-Simple hot
path without changing its inputs, outputs, ordering, or symbol.

The retained five-sample source-matched run measured C median `0.15s` and
Simple median `0.43s`, ratio `2.87x`. A fresh five-sample replay of the same
artifacts measured C median `0.11s` and Simple median `0.32s`, ratio `2.91x`.
Both runs emitted
`checksum=34089754400000000`. The mixed C/Simple coverage executable retained
`branch_outcomes=6/6`. That is 100% coverage only for the three migrated
selection-policy decisions (candidate present, candidate magic, and fallback
magic: both outcomes for each). It is not whole-file C coverage: the frozen
oracle harness reports 46.67% branches, and the memory-acquisition/wrapper
branches in `starfive_runtime.c` remain unmeasured. A source-matched admitted
pure-Simple compiler is not yet available, so the seed result is diagnostic and
must be repeated after the bootstrap critical path completes.

## Acceptance

Retain exact output parity, repeat five warm samples with the same workload,
and require median Simple/C `<= 3.0x`. A faster benchmark with changed inputs,
an inlined C oracle, or a missing checksum is not acceptance.
