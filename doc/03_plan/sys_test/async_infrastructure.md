# Async infrastructure: failure-first acceptance plan

**2026-10-27. Status: planned / UNRUN.** This document creates no test result.
Baseline `32b48baa7b473d7a86557edfc4c3efec81d1b3a6`; existing source/specs were
inspected, not executed. Implements the user's TDD scope, the
[architecture](../../04_architecture/language/async_infrastructure.md),
[detail design](../../05_design/lib/runtime/async_infrastructure.md), and
selected [SRH/resource plan](../lib/concurrent_resources_runner_plan_2026-10-27.md).
Retain all CVC, SRH, release T-*, RR-SOSIX and existing SRA cases; these cases
close integration gaps rather than replace those inventories.

## Test ownership and sequence

Before adding library code or a test helper, inspect existing matching owners,
exports and tests. Extend/adapt them where semantics match. Record the actual
path reused and justify each new API. A second Future, scheduler, registry,
reactor or pointer helper without this comparison fails design admission.

TDD cycle is one failing behavior → minimal change → targeted green → review.
Missing compiler/runtime, import failure, unsupported target or build failure is
**INCOMPLETE/UNSUPPORTED**, not a behavioral RED. Capture it separately. A new
module missing at compile time proves only its API was absent; after it exists,
inject a mapped semantic defect to prove the oracle detects the intended fault.
Do not make a failing case green by replacing the real provider with a fixture.

Run each accepted case once per unchanged implementation/provider combination.
Do not rerun green cases for reassurance. At most six repair cycles per feature;
each retry changes implementation or adds material evidence. Bootstrap limits
and source identities remain those of the bootstrap lane. No tests/builds are
run from this documentation lane.

| Test level | Existing/recommended owner | What it can prove |
|---|---|---|
| Owner-local future/promise tests | `test/01_unit/lib/nogc_async_mut/host_promise_terminal_spec.spl`, `host_future_intensive_spec.spl`, existing async_host handle contracts | Late result sharing, chains, join values, cancellation/error behavior on that provider |
| Scheduler integration | Existing `async_host/async_mutex_suspend_spec.spl`; new focused shared-result cases beside it | Real scheduler parking/wake/cleanup, not just calling poll in a loop |
| Ring tests | Existing `test/01_unit/lib/nogc_async_mut/async_ring/` and integration async specs | Token/generation/state/owner invariants |
| Scalar strict implementation | Active lockless map/ref test and native fixture lane | Real atomic publication/races on its exact native provider, bounded scalar behavior |
| Native host/system cases | Proposed `test/03_system/runtime/async_infrastructure_spec.spl` | Actual sleeping carrier, provider I/O, process closure, source/target evidence |
| Language compile/run and rejection | Existing compiler async/borrow fixture owners; add focused fixtures there | Frame live-value/drop behavior, unsupported syntax, illegal borrow/forgery rejection |
| Modern evidence manuals | Mirrored `.md` under `doc/06_spec/` only, generated after real capture | Readable scenario/evidence documentation; never executable specs there |

System scenario helpers reserved before sidecar implementation:
`step("Request a shared resource")`, `step("Suspend until completion")`,
`step("Observe the same terminal result")`, `step("Cancel one interest")`,
`step("Drain and release the resource")`. Setup helpers:
`open_async_test_scope`, `install_controlled_producer`, `capture_async_trace`.
Checkers: `assert_exact_terminal_inventory`, `assert_independent_progress`,
`assert_retained_owner_safety`. Helpers must invoke real admitted owners and
positive assertions. Missing implementations fail explicitly; never placeholder
PASS or fabricated trace rows. No speculative executable spec is added by
this document-only change.

## Requirement-to-scenario inventory

All rows are **UNRUN** here. Scenario names are planned names, not discovered
test counts. Every row needs exact native/model/provider classification.

| Requirement | Scenario and independent expected result | Owner / existing-plan crosswalk |
|---|---|---|
| AIF-01 Reuse and import consistency | Compile callers through std.async explicit submodules, family-qualified modules, existing async_host/async_embedded aliases; assert same admitted result owner where aliasing is promised; reject unknown/unsupported exports | Facade/resolver; SRH-19/41/48 |
| AIF-02 Native/backend-neutral map contract | Same read/request fixture through strict scalar, native general-map adapter and later pure-Simple provider; exact equality/result identities; overwrite/remove/clear unavailable on insert-once profile rather than silently emulated | Concurrent owner; SRH-01/14/18/19 |
| AIF-03 Shared terminal result | Return promise/future and two refs while pending, complete afterward, observe exact payload/error from all; second completion rejected; non-unit task returns42 and join observes42 | Existing HostPromise/Future/Handle; SRH-02/11/20 |
| AIF-04 Live chains and join | Build pending map(+1), then(child), task join before completion; source41 yields42, child runs exactly once; source failure runs no continuation; retain after initiating caller exits | Existing host combinators/handle; SRH-10/11 |
| AIF-05 Exact concurrent keys | Force equal fingerprints for unequal full keys, concurrent same key and conflicting recipes; exactly one descriptor/ordinary producer per exact key; all i64 boundaries work | Scalar directory; SRH-01/03/14 |
| AIF-06 Helpable claim | Stop winner after descriptor CAS before enqueue; independent requester/executor helps; one admitted start. Full queue leaves discoverable work; no stranded Computing | Registry/executor; SRH-05/06/10 |
| AIF-07 Lost-wake schedules | Complete before check, between check/register, after register before recheck, after Pending; all exact consumers terminate without periodic rescue polling | AsyncRef/subscription; SRH-07 |
| AIF-08 Sleeping executor | Carrier truly enters provider wait; foreign native thread publishes completion during arm/recheck/sleep windows; task resumes once with exact value and unrelated work progresses | Host ingress/provider; extends SRH-07/29/46 |
| AIF-09 Wake identity and saturation | Wrong ring/scope/generation rejected; canceled/ACKed refs not redelivered; NotInFlight retry retained then accepted; zero scan budget reports no progress; real admission exhaustion preserves existing terminal work | Ring adapter; SRH-06/15/47 |
| AIF-10 Independent cancellation | Cancel first of many consumers, others finish; last-interest policy asks producer cancel but does not free until ACK; race delivery/cancel/close with exact interest counts | Resource scope; SRH-08/09/12/47 |
| AIF-11 Retry and effects | Timeout with still-live maker; old resources charged, stale publication fenced; old failed ref remains failed, fresh retry ref succeeds; non-idempotent recipe refused overlapping retry | Registry/admission; SRH-11/12/45 |
| AIF-12 Lifetime and opaque capabilities | Safe generic API rejects foreign/forged/ref after close or compiler rejects construction; pin vs eviction/unmap race; generation exhaustion refuses reuse. Raw unsafe scalar scope destroyed only after joined quiescence; never dereference freed raw storage as a rejection test. Typed wrapper allocation separately recorded | Ref/container owner; SRH-15/16/21/22 |
| AIF-13 Language suspension ownership | Real compiled function preserves live value across delayed await, drops captures once on success/error/cancel; short mutable/table/epoch borrow across await rejected; root block_on works, nested same-executor block_on refused/suspends per profile | Compiler/borrow + existing runtime; SRA language gates |
| AIF-14 Cycles and hard caps | Self-resource recursion and A→B→A wait return diagnostic or supported compiler SCC; nested parent/child work stays under byte/producer caps or reports resource failure | Common TaskRunner; SRH-13/35 |
| AIF-15 Genuine frozen-input I/O | Delayed real provider returns Pending; task parks; independent task completes; filesystem edited afterward cannot change frozen bytes; early completion before park retained; short reads/close errors propagated | Native driver/reactor/SourceReader; SRH-29/31/32 |
| AIF-16 Host/embedded capability honesty | Actual supported atomic width, aligned/misaligned/null probe; strict route never enters legacy mutex handles/allocator fallback; actual post-seal allocation hooks zero only for claimed operations; unsupported target returns explicit result | Native/pure-Simple/noalloc providers; SRH-17/27/28/46 |
| AIF-17 IndexRefFactory | Wrong owner/type/bounds rejected; hash entry reference survives bucket rebuild, repack remaps ordinals; pin retained across admitted suspension, short view forbidden; no serialized runtime address | Memory/container owner; SRH-21…24 |
| AIF-18 ResourceCache and pool separation | Resident hit zero maker/wait allocation/I/O/index rebuild; eviction preserves logical identity; two mutable recycle borrowers never share same checked-out object; reset failure quarantines | ResourceCache/RecyclePool; SRH-04/25/26/40 |
| AIF-19 Common runner execution | Actual BuildRunner/TestRunner dispatch through one owner, typed fiber versus process result, exact child closure, bounded <=128 test groups, executable cache hit cannot mark test executed | Common TaskRunner; SRH-30/33…38 |
| AIF-20 `.rr` recovery and authority | Inject every generation/write/CAS/durability/readback failure: Unknown then entire affected scope reconstructed; root change restarts full scope; exact counts from independent forward manifests; provider TLDR unchanged | Existing SCV/SOSIX; CVC-RR-01…14 / RR-SOSIX-01…12 |
| AIF-21 Independent progress and scale | K/R matrix below; barrier-stalled maker A does not block unrelated B under available budgets; blocked publisher does not block ready reads; exact terminals/no leaks | All adapters; SRH-02…04/35/43, CVC-SCALE-01…12 |
| AIF-22 Compatibility/default gates | Old inputs/schemas/API still work through named adapter; strict capability refusal cannot silently select locked profile; per-file defaults unchanged; required phase3 compiler builds and real Hello receipts from implementation lane | Rollout/bootstrap; SRH-17/19/30/40/48 |

## 3,000 workload and measurement matrix

K=distinct keys; R=outstanding requests; P=admitted producers; W=live waiter
registrations; T=actual OS workers. These quantities are separate. No implicit
3,000-thread launch and no9-million-request cross product.

| Workload | Required result |
|---|---|
| K1/R3000 pending burst | One ordinary maker,3,000 terminal observations, bounded wake batches and shared payload |
| K3000/R3000 independent | Exact one-key-per-request outputs, independent producer overlap within P/bytes |
| K3000/R3000 resident | No maker, no waiter on ready path; allocation and lifetime overhead measured |
| Hot-key skew + cold keys | Disclosed seed/distribution, unrelated result progress and bounded p99 |
| Repeated generations/failure/close | Bounded retired descriptors/epochs, waiter and payload reclamation |
| 2999/3000/3001 and64/65 readiness boundary | Exact explicit capacity result, no truncated ready bitset or dropped event |
| Build/test mixed | Exact output/case inventory;3,000 cases =23 groups of128 +56, bounded process admission |
| Supported embedded capacities | Honest smaller-capacity PASS or typed unsupported/full, no fabricated3000 certification |

Report handle latency separately from first usable result and each request's
terminal latency; p50/p95/p99/max, batch makespan, unique artifact throughput,
joined request throughput, CPU, private/RSS/shared pinned bytes, allocations,
retirement backlog, I/O, and cleanup. Account setup/preallocation, typed boxing,
allocator internals, cold page faults and teardown. Same workload, equality,
payload/retention/durability and validation across native locked, owner-local,
strict atomic and later pure-Simple backends. Set regressions from observed
variance; no arbitrary speedup promises or inherited C++ benchmark winner.

## Evidence and release admission

Every run binds source/producer/test/oracle/policy/target IDs, actual provider
and capability path, cache initial state, worker/process budgets, declared and
executed cardinality, output/trace digests and terminal closure. SDN is the
default receipt format. PASS, FAIL, UNRUN, UNSUPPORTED, INCOMPLETE and QUARANTINED
remain distinct. A modeled schedule or constructed/model-only evidence fixture
cannot qualify native atomics, OS sleep/I/O, memory reclamation, compiler
lowering or bootstrap. An actual native executable fixture may qualify the
production behavior it truly executes, within its stated provider and scope.

Before green admission, inject at least one representative defect per boundary:
duplicate maker, detached join, dropped wake, canceled-waiter redelivery,
stale generation, early unmap, hidden locked fallback, wrong frozen input,
incomplete test inventory. Oracle must fail, then pass after restoration.
Native/backend-specific tests supplement shared contract cases. The design
itself is document-validated only; implementation/native/default-enable gates
remain open.
