# Multicore Green Release Binary Stale Evidence

Date: 2026-06-11
Status: open
Owner: multicore-green lane

## Summary

The checked-in `bin/release/simple` binary is no longer authoritative evidence
for the hosted multicore-green fairness lane.

The checked-in release wrapper and current-source debug artifacts now disagree
on the same lane:

- checked-in `bin/release/simple`:
  - wrapper exists, but its target
    `bin/release/x86_64-unknown-linux-gnu/simple` is missing in this workspace
  - it cannot run even `--version`, so it cannot be cited as hosted
    multicore-green evidence
- current-source `src/compiler_rust/target/debug/simple`:
  - resumable-stepper hosted-native regression specs compile and run the probe
    successfully with `EXIT=0`
  - the historical blocker SSpec and the focused regression SSpec both pass

## Evidence

Current checked-in release wrapper:

```text
bin/release/simple --version
bin/release/simple: line 7: /tmp/simple-mgreen-sliced-jj-1000/bin/release/x86_64-unknown-linux-gnu/simple: No such file or directory
```

Current-source debug hosted-native regression evidence:

```text
src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_resumable_stepper_native_regression_spec.spl --mode=interpreter --clean
PASSED, 1 scenario

src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_resumable_stepper_native_blocker_spec.spl --mode=interpreter --clean
PASSED, 1 scenario
```

Repository state:

```text
bin/release/simple -> wrapper script
bin/release/x86_64-unknown-linux-gnu/simple -> missing
bin/simple -> absent
src/compiler_rust/target/debug/simple -> present
```

## Why This Matters

The fairness/preemption lane cannot rely on the checked-in release wrapper as
proof of current behavior. Current-source debug regression specs are the
stronger evidence for hosted-native closure of the historical lower blockers.

Until the source/runtime/compiler state is made consistent again:

- current-source debug probes are authoritative in this workspace
- checked-in `bin/release/simple` should be treated as stale lane evidence
  rather than a closure signal for multicore-green hosted parity
