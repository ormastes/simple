# Multicore Green Release Binary Stale Evidence

Date: 2026-06-11
Status: mitigated (release platform binary is a generated deploy artifact)
Owner: multicore-green lane

## Summary

The checked-in `bin/release/simple` wrapper is not authoritative evidence for
the hosted multicore-green fairness lane unless its generated platform delegate
exists and passes a probe.

The checked-in release wrapper and current-source debug artifacts now disagree
on the same lane:

- checked-in `bin/release/simple` wrapper:
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

The platform delegate is intentionally not a tracked source artifact:

```text
jj file list | rg '^bin/release'
bin/release/simple
```

`bin/release/` is ignored in both `.gitignore` and `.jjignore`; the platform
binary is materialized by deploy/bootstrap, not committed.

## Why This Matters

The fairness/preemption lane cannot rely on the checked-in release wrapper as
proof of current behavior. Current-source debug regression specs are the
stronger evidence for hosted-native closure of the historical lower blockers.

Until a workspace runs the deploy flow:

- current-source debug probes are authoritative in this workspace
- checked-in `bin/release/simple` should be treated as a probe-required wrapper
  rather than a closure signal for multicore-green hosted parity

The intended local materialization path is:

```text
scripts/bootstrap/bootstrap-from-scratch.sh --deploy
```

That flow installs the full CLI to `bin/release/<platform>/simple` after
building and smoke-testing the bootstrap artifact. The generated platform
binary remains ignored because it is host/platform specific.

## Mitigation

2026-06-13: user-facing wrappers that choose among release/runtime candidates
now require the candidate to pass `--version`, matching the cross-language
profile harness. `bin/sj` and `bin/simple-interp` therefore skip an executable
but stale `bin/release/simple` wrapper whose platform target is missing.
Regression: `test/02_integration/simple_wrapper_runtime_probe_test.shs`.

This closes the multicore-green evidence issue as mitigated: profile and
user-facing wrapper selection must probe candidates and skip stale delegates.
It does not require checking in `bin/release/x86_64-unknown-linux-gnu/simple`.
