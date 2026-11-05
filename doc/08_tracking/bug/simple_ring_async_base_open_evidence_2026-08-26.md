# SimpleRing async-base open evidence

Status: DEFERRED TO PHASE 3

Owner: async runtime/compiler maintainers

Recorded: 2026-08-26

Phase 2 disposition: these findings do not block delivery of the pure-Simple
foundation. They remain qualification debt in
`.spipe/simple-ring-async-base/todo.sdn` and block Phase 3/release/mission
qualification until their exact evidence exists.

## Finding 1: no admissible pure-Simple verification binary

The deployed `bin/simple` resolves to a 60,744,944-byte Rust bootstrap seed and
prints the seed-only warning. Focused specs can diagnose behavior but cannot
satisfy the pure-Simple/SPipe acceptance gate.

Unblock condition: deploy an admitted current pure-Simple Stage 4 binary, record
its identity before and after the run, then execute each command in
`doc/03_plan/sys_test/simple_ring_async_base.md` once and retain explicit
per-file verdicts, docgen `0 stubs`, maintenance, lint, duplicate, and applicable
compiler/lib/MCP/LSP results.

## Finding 2: mission profiles are policy contracts, not static-storage proof

`src/lib/common/contracts/execution/async_profile_v1.spl:282` and `:292` define
fail-closed `mission_alloc` and `mission_pool` policy/capacity records. The
hosted ring allocates its fixed arrays only in
`src/lib/nogc_async_mut/async_ring/simple_ring.spl:123`. The hosted mission
adapter now validates sealed-arena/fixed-pool/frame and task/operation/buffer/
trace/deadline/timer/join-cancellation capacity evidence before `Ready`, and a
bounded trace ring exists. Its receipt deliberately records
`link_time_static_proven=false` and `allocation_free_proven=false`; no linked
static task-pool/arena adapter or memory-upper-bound proof exists yet.

`src/lib/nogc_async_mut_noalloc/async/mission_ready_set.spl` now provides a
scalar-only 64-slot exact-wakeup set with no explicit allocator, collection, or
text storage. Its receipt truthfully leaves compiler-placement,
link-time-static, and backend-allocation-free proof false. The compiler parses
`[T; N]` at `src/compiler/10.frontend/core/parser.spl:927` but drops the size
expression for dynamic Stage4 arrays, so it cannot emit the needed fixed-size
placement receipt.

Unblock condition: bind compiler frame/reservation analysis to `AsyncProfile`,
preserve fixed-array size and placement semantics through lowering/linking, and
retain an allocation trace plus task/ring/pool upper-bound evidence. Until then,
do not claim mission runtime
qualification or zero-allocation proof beyond the hosted ring's steady-state
scalar path.

## Finding 3: compiler/runtime still contain blocking async compatibility paths

`src/compiler/10.frontend/desugar/desugar_async.spl:217` still lowers explicit
await through the legacy path, and
`src/compiler_rust/runtime/src/async_runtime.rs:128` calls
`rt_future_await`. These are outside the V1 base-contract implementation but
prevent an end-to-end “all executors poll and never block” claim.

Unblock condition: lower await to the shared typed frame/poll ABI, remove
blocking waits from executor poll paths, and demonstrate delayed I/O where an
unrelated task progresses, with zero executor-thread blocking events.

## Finding 4: performance and universal concurrency proof remain unmeasured

The deterministic integration specs cover representative interleavings but are
not a race/fairness proof. The ring now exposes batch/kick and caller-clock
completion-latency telemetry, a real benchmark spec records p50/p99/p99.9 and
throughput, and the trace ring captures typed causal events. The bounded model
spec exhausts all 117,649 capacity-one traces of length six, with its source
linearization map retained in `doc/09_report/evidence/`. This is finite safety
evidence, not a concrete refinement, arbitrary-capacity proof, thread/memory
model proof, or fairness result. No admitted before/after baseline or
RSS/allocation receipt exists.

Unblock condition: run the representative fixture plan from
`doc/03_plan/sys_test/simple_ring_async_base.md` on an admitted pure-Simple
binary, add a concurrency/resource model for ownership and cancellation
linearization, mechanize the remaining concrete/arbitrary-capacity and liveness
obligations, and retain the measured receipts. A single interleaving, bounded
trace depth, or source inspection must not close this finding.

## Evidence run 2026-11-05 (diagnostic lane, worktree work/libbug-w6-ring-20261105)

Environment: worktree `/tmp/wt-libbug-w6-ring` on `origin/release/1.0.0`
(adfeae3765c; identical to main HEAD for every file in this lane). Host aarch64
Linux. `bin/simple` is absent in the worktree, so the plan commands were executed
with the substitute CLI
`/home/yoon/dev/simple/build/phase_snapshots/phase1_1793422538/simple`.
IMPORTANT (per Finding 1): that binary is the Rust bootstrap seed
(43,367,912 bytes, v1.0.0-rc.1, prints the seed-only warning). Everything below
is diagnostic evidence only; it does NOT satisfy the pure-Simple/SPipe
acceptance gate and does not close Finding 1.

Binary identity: sha256 424d712cda338669d26121495041531b63cb67e30a1b07151e9a026c2d813cd6
recorded before and after the run — identical.

Open-path audit (async-first): no ring/transport `open` function exists. The
async-base open handshake is `SoftwareRingProvider.create` ->
`admit`/`admit_for_depth` (pure profile validation, no I/O, no waits, no
blocking primitive) followed by nonblocking poll via `poll_future_compat`,
whose `FutureCompatReceipt` records `blocking_used=false` and
`scheduler_created=false`. Mission profiles carry `blocking_allowed=false`.
The open path is async-first as designed; no broken/incomplete component was
found, so no TDD fix was required.

Per-file native verdicts (`SIMPLE_NO_STUB_FALLBACK=1 ... test <file>
--mode=native`), logs under `build/test-artifacts/simple_ring_async_base/native/`:

- simple_ring_async_v1_spec: OK 10/10
- async_profile_v1_spec: OK 18/18
- simple_ring_spec (async_ring): OK 9/9
- mission_adapter_spec: OK 10/10
- async_trace_ring_spec: OK 9/9
- mission_ready_set_spec: OK 6/6
- simple_ring_async_base_integration_spec: OK 2/2
- simple_ring_profile_integration_spec: OK 4/4
- simple_ring_future_compat_spec: OK 3/3
- simple_ring_async_base_concurrency_spec: OK 5/5
- simple_ring_async_base_bounded_model_spec (117,649 traces): OK 1/1
- simple_ring_async_base_spec (system/SPipe): OK 7/7
- simple_ring_async_base_perf_spec (p50/p99/p99.9, throughput, high-water): OK 2/2

All native runs carry `degraded=mcdc-unavailable:compiler-lacks-probe-emission`;
interpreter cross-check of the same files is also fully green. Zero dropped
examples, zero failures.

Regression (neighboring ring/transport/async specs, interpreter, all OK):
simple_ring_rti004_wa_spec 6/6, poll_spec 2/2, scheduler_spec 2/2,
wcet_adapter_spec 3/3, async_ref_interest_contract_spec 3/3,
async_ref_wake_contract_spec 3/3, lockless_map_async_ref_spec 4/4,
lockless_map_boundary_contract_spec 1/1.

Gate results:

- `check src/lib ...` (plan line 1): FAIL-fast (exit 1) without a self-hosted
  worker: "ERROR: no admitted cached self-hosted check worker artifact is
  available ... deploy bin/release/<triple>/simple or set SIMPLE_BINARY".
  With `SIMPLE_BINARY=<seed>` the check proceeded through 17,381 log lines with
  zero errors but did not complete within the session budget (~16 min) and was
  terminated; no verdict is claimed. This is Finding 1's blocker reproduced.
- `spipe-docgen`: generated 1 doc, 0 stubs; however the seed tool's output
  regressed the committed manual (-78 lines), so the regenerated file was
  reverted and this is recorded as diagnostic-only.
- `sspec-maintain scan`: BLOCKED — command not present on the seed binary
  ("error: file not found: sspec-maintain").
- Layout guard `find doc/06_spec -name '*_spec.spl' | wc -l`: 0.
- `scripts/audit/direct-env-runtime-guard.shs --working`: STATUS: PASS.
- `scripts/audit/direct-env-runtime-guard.shs --staged`: STATUS: PASS.

Disposition: the async-base open path is functional and async-first at the
spec level (all 13 plan spec files green on the substitute binary). Finding 1
remains BLOCKED on SRA-P3-001 (deploy an admitted pure-Simple binary); Finding 3
(await lowering / rt_future_await) and Finding 4 (perf/concurrency proof) are
unchanged by this run. Raw logs and receipts:
`build/test-artifacts/simple_ring_async_base/` (gitignored).
