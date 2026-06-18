<!-- codex-design -->
# GPU Web and DB Offload Agent Tasks

Status: crash-session plan recovered; benchmark-harness implementation in
progress.

## Crash-Session Continuation

The prior Codex rollout was found at
`/home/ormastes/.codex/sessions/2026/06/16/rollout-2026-06-16T04-07-18-019ece9c-bb30-76a1-952f-7233322187d1.jsonl`.
The current authoritative continuation surface is the worktree, especially
`doc/03_plan/perf/gpu_web_db_offload_optimization_benchmark_plan.md`, because
the recovered plan and harness artifacts have advanced beyond the original
crash note.

Fast continuation check:

```sh
scripts/check/check-gpu-web-db-offload-recovery-harness-self-tests.shs --check-current-artifacts
```

That check verifies the durable web, DB, readiness, recovery, env-template,
setup-checklist, and missing-by-category artifacts without rebuilding native
targets or rerunning live benchmarks.

## Crash-Session Follow-On Plan

1. Preserve the already-green reverse-proxy crash recovery gates:
   live reverse proxy, upstream pool reuse, upload streaming, and upgrade tunnel.
2. Add deterministic production-hardening evidence for the next proxy lane:
   timeout state, request/upload backpressure, downstream response
   backpressure, upstream pool pressure, and measured throughput.
3. Keep the first implementation slice in pure policy helpers and unit specs so
   worker/live gates can consume the same decisions without adding flaky crash
   reproduction loops.
4. Regenerate the async reverse-proxy spec manual and append status evidence to
   `doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md`.
5. After the pure helper is green, wire the evidence into the live worker/report
   path and then resume broader GPU DB/web throughput benchmarking.

## Current Scope

The pure async reverse-proxy hardening helper, focused unit coverage, report
row, web/DB benchmark rows, readiness wrapper, and recovery harness are already
implemented. Continue by either filling external fixtures from the generated
setup checklist or by extending the benchmark matrix with another measured
producer that preserves the existing strict producer/consumer contracts.

Do not re-run already-green live crash gates in this session unless a touched
file invalidates their evidence.
