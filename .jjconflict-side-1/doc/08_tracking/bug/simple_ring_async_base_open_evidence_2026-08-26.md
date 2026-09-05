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
