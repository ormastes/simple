# Parallel implementation plan: incremental build metadata

<!-- codex-design -->

Status: detailed plan with Astra design-only acceptance after contract corrections. User priority: this optimization design first, bootstrap continues independently. No proposed task is marked implemented by this plan.

## Current four-agent allocation

| Slot | Owner | Current deliverable |
| --- | --- | --- |
| 1 | Root | Integrated architecture, detailed contracts, acceptance map, source review and eventual merge coordination |
| 2 | Astra semantic reviewer | Full supplied-research review, invalidation/ownership/race findings and formal obligations |
| 3 | Performance/memory reviewer | Measured bottlenecks, source dependency audit, latency/I/O/RSS budgets and regression plan |
| 4 | Bootstrap agent | Continue Phase3 to end, preserve successful objects, collect Phase4 failures, validate changed-input MCP workaround |

Lower-model sidecars: N/A for this pass; four slots are occupied and the work changes compiler correctness boundaries. Root owns integration; Astra reviews semantic correctness; the performance reviewer reviews memory/cost tradeoffs. No agent may edit another lane's files without explicit handoff.

## Work packages and dependencies

| Package | Ownership boundary | Depends on | Acceptance / handoff |
| --- | --- | --- | --- |
| W0 baseline | Counters, source/body/toolchain bytes, process launches, phase timing, retained failure groups | Existing build | Same-source baseline matrix; no claimed attribution from aggregate I/O alone |
| W1 contracts | Common source-change DTOs, adapters to existing snapshot/gateway, canonical codec rules | Reviewed design | Round-trip/golden tests, no duplicated authority or platform handles |
| W2 immediate latency | Parse fanout, TLDR consumer dependency split/batch scans, redundant toolchain hash | W0, existing contracts | Native correctness + memory + phase-level performance checks; independent patches |
| W3 generation sharing | Snapshot provider, refresh publisher, immutable reader leases | W1 | Concurrent reads avoid per-worker whole-tree refresh; overflow/crash/stale-generation tests |
| W4 shared artifacts | Stage-specific single-flight, AST/header sharing, SCC scheduling, async I/O/backpressure | W1,W3 | Exactly one publisher per full key; no waiter deadlock; header available before object |
| W5 metadata adapters | IDE/Spipe/SCV events and private standalone sink | W1 | Equal semantic deltas across adapters; audit origins remain distinct; reconcile unwrapped edits |
| W6 SCV migration | Existing metadata/WAL owner, recovery and bounded segments | W1,W5 | Idempotent migration, torn-tail recovery, single durable owner |
| W7 freshness | Existing TLDR headers, scope/read-set verifier, exact inventory receipts | W1,W3 | Fresh/full versus reused/delta parity; negative-query and static-guard coverage |
| W8 post-build | Existing task journal/scheduler, TestRunner coordinator, qualification join | W7 | Binary publication precedes residual work; pending cannot pass required gates |
| W9 SCM association | Git notes/SCV revision adapters and conflict-aware index | W6,W7 | Exact immutable target; no source amend; default remote/source-commit side effects off |
| W10 deeper optimization | Region parser reuse, precise read sets, hybrid SMF and selective runtime closure | W2,W4,W7 | Each feature independently benchmarked and differential-tested; packed compatibility |

The entire supplied scope is retained. Compiler critical-path improvements W2/W3 are moved earlier than editor/SCM integration because the user's immediate problem is bootstrap latency. This does not turn receipt publication into a substitute for fixing compilation.

## Waves with bounded parallelism

Wave A: bootstrap remains in slot 4; root freezes interfaces; semantic and performance reviewers complete independent findings. Existing source-only MIR and TLDR candidates stay isolated until reviewed and tested.

Wave B: one lane implements W2, one W3, root implements/reviews W1 and model/spec contracts, bootstrap continues. W2 files are separate from source-change/SCV ownership. Combine only tested changes into a new pinned compiler candidate; do not mutate live bootstrap source.

Wave C: W4 starts after W1 and W3; W5 starts after W1, and W6 follows W1 and W5. These lanes may overlap once their prerequisites pass; root owns W7 integration. Bootstrap uses qualified candidates as available. W8/W9 can develop against frozen receipt interfaces, but cannot claim native success before W7 runs.

Wave D: W10 optimizations follow proven cache correctness. Remote transport/authorized asynchronous source commits remain later optional scope, never prerequisites for the Windows compiler.

## CPU, memory and process policy

The shared host limit is 80 scheduled CPU jobs, not 80 per lane. Allocate 20 jobs per independent build/test lane when four workloads are runnable; permit 40 when capacity is available and reduce link concurrency according to observed memory. Exercise 128 logical HIR workers in scalability tests without hard-coding that as a host resource grant. Idle waiters release CPU credits.

The proposed normal worker shape is four module threads per process, each with private mutable compilation state and shared immutable artifacts. Count runnable module threads, not processes, against the shared 80-job pool. Waiting releases CPU credits but retains accounted memory and reader pins until safely released. Native backend/thread-safety and state-reset tests must pass before enabling it. Crash recovery isolates affected/unknown tasks; normal diagnostics continue grouped execution. Memory monitoring remains explicit; an over-budget measurement is not a memory PASS even when a diagnostic bootstrap is allowed to continue.

## Bootstrap continuity and retry discipline

Keep the active 6bf source holder immutable. Cached passing modules are not rebuilt merely because another lane failed. Continue independent phase/tool tasks and preserve successfully emitted objects after aggregation failure. Record failure stages separately: admission, parse, HIR finalization, MIR, backend, aggregation, final link, runtime and test verdict.

No unchanged compiler retry is justified by a new plan. At most three changed-input verification cycles apply to each repair; then retain the bug and escalate its next action. Workarounds require a bug identity, exact patch/source binding and a verification condition for removal. Removing a workaround follows application and validation of the real fix, not merely fetching its commit.

## Landing and release

Review exact candidate sources and tests, preserve unrelated dirty work, and land through reviewed PRs to the requested release branch. Documentation may describe unimplemented work honestly; runtime changes require actual relevant qualification. Windows RC1 still requires the requested bootstrap and product gates. Linux/macOS/BSD remain RC2 release targets, while portable schema tests are part of this design's correctness scope.
