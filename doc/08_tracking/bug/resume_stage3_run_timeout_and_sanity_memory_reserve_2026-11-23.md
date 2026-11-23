# Stage 3 resume sanity: `run_timeout` missing (127) and memory reserve scrubbed

- **Date:** 2026-11-23
- **Status:** fixed on `work/resume-stage3-run-timeout-20261123` (base `release/1.0.0` `842a5adeefe`)
- **Host:** Windows `DESKTOP-VMF96U6`, Git Bash
- **Impact:** a canonical Stage 3 resume whose BUILD passed
  (`stage3-native-build-status.env` `status=pass`) failed sanity, so a good
  Phase 3 compiler was not admitted.

## Defect 1 — `run_timeout: command not found`

`scripts/bootstrap/resume-stage3-from-admitted.sh` `bootstrap_stage_sanity`
(at `842a5adeefe`: lines 1389 and 1396) calls `run_timeout` for the
`--version` and unsupported-command probes. The function was defined only in
`scripts/bootstrap/bootstrap-from-scratch.sh:2052`. The resume runs as its own
process and never sources that file, so both probes exited **127**:

```
resume-stage3-from-admitted.sh: line 1379: run_timeout: command not found
```

`test/02_integration/bootstrap_stage3_resume_from_admitted_test.shs:374`
stubs `run_timeout` inside its fake admission file, which is why it never
caught this.

A census of every function defined in `bootstrap-from-scratch.sh` that the
resume calls in command position found `run_timeout` as the only one missing
(`usage` matched only inside `${1:?usage: ...}`).

**Fix:** moved the one definition to `scripts/bootstrap/lib/run-timeout.shs`;
`bootstrap-from-scratch.sh` and `resume-stage3-from-admitted.sh` both source
it. `scripts/bootstrap/lib/requalify-stage2-worker.shs:135`, which
extracted the body from `bootstrap-from-scratch.sh` with awk, now extracts it
from the lib. Without that change it would have produced an empty function
file and hit the same 127.

## Defect 2 — frontend smoke refused at a 24576 MiB reserve

```
error: build refused: 17856 MiB of RAM/commit headroom free, below the 24576 MiB reserve (SIMPLE_BUILD_MEMORY_RESERVE_BYTES)
```

This happened even though the caller exported `SIMPLE_BUILD_MEMORY_RESERVE_BYTES=2147483648` and
`config/host/DESKTOP-VMF96U6.sdn:48` sets `mem_reserve_free_mib: 2048`.

Root cause:
- The resume sanity's env scrub (`resume-stage3-from-admitted.sh`, the
  `for name in $(env ...); unset` loop in `bootstrap_stage_sanity`) unset
  `SIMPLE_BUILD_MEMORY_RESERVE_BYTES` along with `COMPUTERNAME`/`HOSTNAME`.
- `build_memory_reserve_kib()` (`src/app/cli/shard_mem_clamp.spl:1031`) then
  found no env value.
- `host_limit_mem_reserve_free_kib` could not resolve the hostname
  (`src/lib/nogc_sync_mut/host_limits.spl:37-44`).
- The compiler therefore fell back to the total-RAM rule, capped at
  `BUILD_MEMORY_RESERVE_CAP_KIB_V1 = 25165824` KiB, which is 24576 MiB
  (`src/app/cli/shard_mem_clamp.spl:1015-1020`).

`bootstrap-from-scratch.sh`'s own `bootstrap_stage_sanity` already preserved
the variable (validation `:2936-2958`, re-export `:3040-3043`). The resume
copy never received that pass-through.

**Fix:** the resume's `bootstrap_stage_sanity` now uses the same validated
pass-through:
- It captures the variable before the scrub and re-exports it afterwards.
- It returns 125 with `reason=invalid-build-memory-reserve` for a malformed,
  zero-prefixed, sub-KiB or overflowing value.
- When the variable is unset, it stays unset and the compiler keeps its
  default (today's behaviour).

The host config's `mem_reserve_free_mib` is honoured because
`bootstrap_host_apply_memory_reserve` (`resume-stage3-from-admitted.sh` after
`lib/host-bootstrap-settings.shs`, `host-bootstrap-settings.shs:33-37`) folds
it into the same env var before the sanity step runs.

## Regression test

`scripts/bootstrap/tests/resume-stage3-sanity-helpers-test.shs` runs the
real extracted `bootstrap_stage_sanity` against a fake candidate, using only
the libs the script sources itself and no `run_timeout` stub. It checks:
- the version probe status is 0;
- the unsupported-command probe status is 1;
- the reserve reaches the frontend smoke when set, stays absent when unset,
  and returns 125 when malformed.

It also runs the helper census. Its fatal selftest replays both regressions
and the `842a5adeefe` script. Against that script it reports `version probe
status 127`, `unsupported-command probe status 127`, `census: run_timeout`
and `want 2147483648`.
