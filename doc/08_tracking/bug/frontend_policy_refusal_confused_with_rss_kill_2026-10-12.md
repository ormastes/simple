# Frontend product-policy refusal confused with an RSS kill (cycle 22, 2026-10-12)

Date: 2026-10-12. Lane: release_phase3 self-host bootstrap campaign.
Status: DIAGNOSED; diagnostic improvement landed (refusal-evidence line).
Not a policy wall; not a units bug; not an RSS kill.

## Symptom

Cycle 22 stage2 compiler-tests: every artifact build (mcp_build,
compiler_cli_build, test_runner_build, lsp_build) recorded
`result=FAIL|status=88|elapsed_seconds=0|max_rss_kib=unavailable`, with the
build log containing exactly one line:

```
bootstrap-phase-verification: frontend product policy refused: cap_kib=6835937 ceiling_kib=6835937 workers=4
```

This was initially read as the tree-RSS watchdog's `rss-cap-exceeded` 88 (the
same numeric status the watchdog emits at cap), sending the investigation
toward budget knobs and memory measurement.

## Actual cause

`run_task` maps the pre-exec policy refusal `bootstrap_phase_c_apply_frontend_policy || exit 88`
(bootstrap-phase-verification.shs) to the same status 88 as the watchdog's
kill. The refusal itself was caused by an AMBIENT environment knob:
`SIMPLE_BOOTSTRAP_FRONTEND_MEMORY_BUDGET_KIB=4194304` (an experiment to raise
the frontend share) inherited by the campaign launch. The product policy
pins the frontend share at 3000000 KiB BY DESIGN
(`bootstrap_stage3_windows_frontend_environment` refuses any budget > 3000000),
so every artifact build refused at elapsed 0. No compiler process ever ran;
the RSS watchdog was never reached.

Verified by replaying the policy chain in isolation: clean env passes
(share 3000000, cap 6835937, ceiling 6835937); adding only
SIMPLE_BOOTSTRAP_FRONTEND_MEMORY_BUDGET_KIB=4194304 refuses. An mcp artifact
build with the verifier's flags under the cycle-22 stage2 candidate, clean
env, default budgets, threads=4: NO refusal, NO RSS kill; it ran ~5.5 min and
failed only at the known next layer (`MIR module has no functions or static
data`, 19 units -- see stage2_full_cli_artifact_layer_2026-10-12.md).

## About the older RSS-kill 88s

The watchdog's 88 (`scripts/resource/process-tree-rss-watchdog.pl`, status
`rss-cap-exceeded`) fires when the SUMMED RSS of every process-group member
exceeds the cap. Historical 8-worker kills at ~5.6-5.9 GiB were tree sums of
parallel shard workers (per-process peaks ~2.2 GB each) -- the cap working as
designed, not a measurement bug. The serialized configuration
(BOOTSTRAP_VERIFY_TEST_WORKERS=1, BUILD_THREADS=4) keeps the sum well under
the 6.5 GiB ceiling.

## Fix landed

`scripts/bootstrap/phase-c-backend-commands.shs`: on product-policy refusal,
in addition to the pinned refusal line (kept verbatim for
phase-c-preflight-policy-test.shs), print a stderr-only evidence line naming
the three fail-closed inputs with their observed values: the frontend budget
(with the 3000000 pin), and the four inherited shard knobs with their exact
required values. Verified: phase-c-preflight-policy-test.shs still PASSes, and
the poisoned-knob replay now prints
`frontend_budget_kib=4194304 (pinned maximum 3000000; larger values refuse by design)`.

## Operator guidance for cycle 23

Launch with a clean environment: do NOT export
SIMPLE_BOOTSTRAP_FRONTEND_MEMORY_BUDGET_KIB (any value > 3000000 refuses by
design; the knob cannot raise the frontend share). The serialized
TEST_WORKERS=1 / BUILD_THREADS=4 configuration is sufficient memory-wise; the
remaining artifact-build blocker is the AOT empty-module layer, not memory.
