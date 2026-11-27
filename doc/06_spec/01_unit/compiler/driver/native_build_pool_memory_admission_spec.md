# Native-build pool memory admission

Hand-maintained companion to `test/01_unit/compiler/driver/native_build_pool_memory_admission_spec.spl`.
This document is not canonical docgen output and does not claim that the SSpec
suite has executed. Source SHA256: `642b1cd3404783f19911fc07a935165847f5c635857d11a6ad57e28f4cf2b269`.

## Scope and expected behavior

The 19 scenarios cover worker estimate floors, host-memory capacity, explicit
worker overrides, and the effective tree budget. Known host free RAM/commit is
reduced by the configured reserve before compiler caps are applied. A missing
host measurement retains the conservative cap-minus-reserve fallback. The
coordinator reservation and two-worker minimum remain separate checks.

## Requirements and oracles

| Requirement | Relevant scenarios / native fixture |
|---|---|
| REQ-HR-01 | Known-host-free tightening and explicit reserve/declared-cap scenarios; native cases 2–4 and 8. |
| REQ-HR-02 | Exact mirgen2 scoped-cap scenario; native case 1. |
| REQ-HR-03 | Unknown-host-free, no-cap and no-measurement branches; native cases 5–7. |
| REQ-HR-04 | Existing worker estimate and capacity scenarios; source review confirms parent admission unchanged. |

The measured mirgen2 input is declared/cap 25,165,824 KiB, host free 97,608,600
KiB, reserve 25,165,824 KiB; the expected effective budget is 25,165,824 KiB.
A 64 GiB cap, 30 GiB host free and 24 GiB reserve instead yield 6 GiB. These
oracles follow the host policy, not the implementation's intermediate values.

## Scenario inventory

- budgets cover the largest measured worker peak
- MIR budget is below the old refusing constant
- admits a pool of 2 workers with 32 GB free
- refuses the pool (cap <= 1) with 24 GB free
- refuses the pool (cap <= 1) with 1 GB free
- refuses with unknown host memory
- ignores a 1.36 GB parent peak: estimate covers 3.4 GB worker peaks
- uses the MAX recorded worker peak, not the mean
- uses the default with no recorded peaks
- a light-lane record never lowers the default (fail-closed)
- a 12 GB recorded peak raises the estimate
- a deliberate override wins
- declared 90 GB with a 64 GB cap gives 40 GB
- falls back to free commit when no cap is set
- keeps the host reserve outside a smaller scoped compiler cap
- tightens a large compiler cap when actual host free memory is low
- preserves explicit host reserve and smaller declared budgets
- a declared budget below the clamp is kept
- a cap of 24 GB or less refuses when host free memory is unknown

## Execution and retained evidence

The companion SSpec has 19 executable scenarios; its full runner status is
**pending**, because the deployed self-hosted test CLI is unavailable. Root is
building an isolated full CLI; no seed test result is substituted.

`test/fixtures/bootstrap/host_reserve/main.spl` imports the production helper
and checks eight values. The same fixture exited 1 before repair and printed
`PASS: 8 host-reserve arithmetic assertions` with exit 0 afterward. Producer,
backend, capsule, artifact hashes and retained log paths are recorded in
`doc/08_tracking/bug/shard_host_reserve_scoped_cap_2026-11-06.md`.

## Workflow, limitations and recovery

Run the SSpec with the newly qualified self-hosted CLI once available, then
record actual counts and failures. Do not infer suite success from native
helper success or linking. The corrected 24 GiB effective budget still admits
only one worker under the separate current parent/worker policy, so Phase 3
remains unqualified. Preserve rejected producer receipts and investigate that
remaining boundary without lowering reserve configuration or weakening guards.
