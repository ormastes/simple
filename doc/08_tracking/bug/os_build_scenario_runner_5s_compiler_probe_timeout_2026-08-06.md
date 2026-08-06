# Bug: `bin/simple os build/test --scenario=...` compiler-discovery probe times out at 5s, fails ALL scenarios

**ID:** os-build-scenario-runner-5s-compiler-probe-timeout-2026-08-06
**Domain:** os/simpleos build tooling (`src/os/_QemuRunner/os_build_run.spl`)
**Severity:** blocker (for every `bin/simple os build`/`os test --scenario=...` invocation
in this environment)
**Filed:** 2026-08-06

## Summary

While pushing the riscv64 SimpleOS boot campaign forward, `bin/simple os test
--scenario=riscv64-hosted` and `--scenario=riscv64-smoke` both failed
immediately with:

```
[build][riscv64] phase=tooling FAILED: no runnable pure-Simple compiler
Error: build failed for scenario riscv64-hosted
```

This is not riscv64-specific — it is a compiler-discovery bug that fails the
scenario runner for every target in this environment.

## Root cause

`_simple_binary_has_native_build_contract` (`src/os/_QemuRunner/os_build_run.spl:436-449`)
probes each compiler candidate with:

```
_run_candidate_admission_pinned(candidate, probe_args, 5000)   # 5000ms hard timeout
```

The self-hosted `bin/simple` binary in this environment takes materially
longer than 5s to even reach its own argument-validation error path. Direct
reproduction:

```
$ time timeout 5 bin/simple native-build --backend cranelift \
    --entry src/app/cli/main.spl --mode definitely-invalid-mode
Terminated
real 0m5.005s   # killed by the probe's own timeout, produced no output

$ time timeout 60 bin/simple native-build --backend cranelift \
    --entry src/app/cli/main.spl --mode definitely-invalid-mode
[STDERR] error: native-build worker exited with code 1. ...
real 0m16.370s  # the actual diagnostic the probe is looking for
```

Every candidate in `_find_simple_binary_for_target`'s candidate list
(`release/x86_64-unknown-linux-gnu/simple`, `bin/simple`, etc.) is subject to
the same 5000ms bound, so all of them silently fail the probe and
`_find_simple_binary_for_target` returns `""`, which the caller
(`build_os_with_backend`, line 205-209) reports as "no runnable pure-Simple
compiler" — a misleading message; the compiler is runnable, just slower than
the probe allows.

## Impact

`bin/simple os build --scenario=<any>` and `bin/simple os test
--scenario=<any>` are currently unusable in this environment. Direct
`native-build` invocation (bypassing the scenario runner, mirroring the
pattern in `scripts/os/ssh_simple_hello_uefi.shs`) still works and is the only
way today to build any SimpleOS kernel target.

## Fix

Raise `_run_candidate_admission_pinned`'s timeout for this probe (or make it
configurable via env, matching the `SIMPLE_OS_BUILD_TIMEOUT_MS` pattern already
used elsewhere in the same file) to comfortably exceed self-hosted `bin/simple`
cold-start cost (observed ~16s here; should not be hardcoded to 5s).

## Related

- `doc/08_tracking/bug/riscv64_kernel_codegen_blocker_2026-07-20.md` (update
  2026-08-06) — the actual riscv64 kernel build blocker once this probe is
  bypassed.
