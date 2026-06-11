# Multicore Green Release Binary Stale Evidence

Date: 2026-06-11
Status: open
Owner: multicore-green lane

## Summary

The checked-in `bin/release/simple` binary is no longer authoritative evidence
for the hosted multicore-green fairness lane.

Current-source rebuilt release artifacts and the checked-in release binary now
disagree on the same probes:

- checked-in `bin/release/simple`:
  - helper-return function-value native probe passes
  - resumable-stepper probe fails earlier at compile time with
    `undefined symbol: rt_pool_is_done`
- current-source rebuilt `src/compiler_rust/target/release/simple`:
  - helper-return probe compiles, but the native binary crashes with `EXIT=139`
  - resumable-stepper probe compiles, but the native binary crashes with
    `EXIT=139`

## Evidence

Current-source rebuild:

```text
cargo build --release -p simple-driver
Finished `release` profile [optimized] target(s) in 2m 09s
```

Current-source rebuilt helper-return probe:

```text
src/compiler_rust/target/release/simple compile /tmp/helper_return_fn_value_probe.spl --native -o /tmp/helper_return_fn_value_probe_rebuilt_release.bin
Compiled ... -> /tmp/helper_return_fn_value_probe_rebuilt_release.bin

/tmp/helper_return_fn_value_probe_rebuilt_release.bin
direct=7
Segmentation fault (core dumped)
EXIT=139
```

Current-source rebuilt resumable-stepper probe:

```text
src/compiler_rust/target/release/simple compile build/test/multicore_green_resumable_stepper_native_blocker/resumable_stepper_probe.spl --native -o /tmp/resumable_stepper_probe_rebuilt_release.bin
Compiled ... -> /tmp/resumable_stepper_probe_rebuilt_release.bin

/tmp/resumable_stepper_probe_rebuilt_release.bin
Segmentation fault (core dumped)
EXIT=139
```

Checked-in `bin/release/simple` mismatch:

```text
bin/release/simple compile build/test/multicore_green_resumable_stepper_native_blocker/resumable_stepper_probe.spl --native -o /tmp/resumable_stepper_probe_release.bin
error: codegen: undefined symbol: rt_pool_is_done
```

## Why This Matters

The fairness/preemption lane cannot rely on the checked-in release binary as
proof of current behavior. Current-source rebuilt release and debug binaries are
the stronger evidence for the remaining hosted-native blocker.

Until the source/runtime/compiler state is made consistent again:

- current-source rebuilt release/debug probes are authoritative
- checked-in `bin/release/simple` should be treated as stale lane evidence
  rather than a closure signal for multicore-green hosted parity
