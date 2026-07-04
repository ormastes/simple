# Multicore Green Stress Scale Blockers - 2026-06-07

Status: likely-fixed (triaged 2026-06-11, evidence: resolved/fixed content in body)

## Summary

Resolved. The current Docker-isolated cross-language stress profile includes a
compact Simple multicore-green native row at 1000 tiny workers with
`pool_used=1000/1000` evidence.

## Evidence

- The original generated 512-worker unrolled `multicore_green_spawn` stress
  source timed out during native compile under the profile smoke budget.
- Root cause for the compact handle-array checksum mismatch was parent
  local/parameter capture in outlined Simple lambdas. `ClosureCreate` stored
  captures in the closure struct, but the outlined body read rewritten local
  slots instead of hydrating them from that closure object.
- The compiler now maps captured parent locals into outlined lambda-local slots
  and Cranelift hydrates them from closure offsets before executing the body.
- The checked-in profile script generates compact handle-array fanout for
  `multicore_green_spawn`. The current Docker contract report records
  `pool_used=1000/1000` for Simple multicore green native stress.

## Impact

- The checked-in Docker contract profile uses `FANOUT_STRESS_WORKERS=1000`.
- The unrolled many-spawn compile timeout remains a generator-size problem, but
  it no longer blocks the profile because the harness uses compact Simple code.

## Follow-Up

- Keep reducing native compile cost for generated many-spawn Simple workloads.
