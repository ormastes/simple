# Seed test-runner kills the spec child at ~600s regardless of --timeout

**Date:** 2026-08-02 · **Severity:** high (blocks long system specs) · **Area:** test runner / seed delegation

## Symptom

`SIMPLE_TIMEOUT_SECONDS=3600 bin/simple test <spec> --timeout 1700` on a
long-running system spec (observed with
`test/03_system/gui/web_showcase_full_gpu_offload_spec.spl`, ~12-node document
rendered repeatedly under the tree-walk interpreter) dies with
`Process timed out`, exit 255, at a fixed ~600s wall clock — the `--timeout`
value and `SIMPLE_TIMEOUT_SECONDS` are NOT honored by the outer seed
delegation for the child. The child process is the *debug* seed
(`target/debug/simple` via test_runner_single).

## Impact

- Any spec whose honest interpreter runtime exceeds ~600s cannot produce a
  green `Results:` line through the `bin/simple test` lane at all.
- The showcase spec's green evidence (13/13, commit 8685764f5bf) was captured
  via the release-seed `bin/simple run` child instead (same child spec
  semantics, no broken outer bound) — suite integration of that spec waits on
  this fix.
- Distinct from the 60s/95%-CPU kill_simple_monitor daemon (which
  `SIMPLE_TIMEOUT_SECONDS` does bypass) — this is a second, harder bound in
  the runner's bounded-wait.

## Expected

`--timeout N` (and/or `SIMPLE_TIMEOUT_SECONDS`) propagates to whatever
bounded-wait the outer runner imposes on the spec child; no fixed 600s
ceiling.

## Repro

Run the showcase spec as above on a loaded box (interpreter + contention
pushes it past 600s); observe exit 255 + `Process timed out` at ~600s while
the child was still progressing (per-thread utime still advancing).
