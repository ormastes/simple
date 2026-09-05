<!-- codex-design -->
# Simple Ring and Async Base — System Test Plan

## Scope and evidence boundary

This plan covers the V1 pure-Simple ring/task contract and the bounded software
provider. It does not claim native io_uring, device/NVMe, compiler implicit-await
lowering, or executor migration; those are follow-on conformance lanes. The
authoritative executable system scenario is:

`test/03_system/runtime/simple_ring_async_base_spec.spl`

Its required SPipe mirror is:

`doc/06_spec/03_system/runtime/simple_ring_async_base_spec.md`

## Phase boundary

Phase 2 accepts the pure-Simple source foundation, the authored tests/manual,
and the retained bootstrap-seed diagnostics as implementation feedback—not as
qualification evidence. The full execution matrix below is Phase 3 and is
authoritatively queued in `.spipe/simple-ring-async-base/todo.sdn`. Therefore a
missing admitted self-host, coverage receipt, docgen receipt, benchmark, or
static-placement proof does not reopen Phase 2; it keeps its Phase 3 row TODO.

The evidence family is deliberately split so a unit result cannot be promoted to
an integration, performance, concurrency, or formal result:

| ID | Evidence surface | Frozen path and purpose |
|---|---|---|
| U | Unit | `test/01_unit/lib/common/contracts/execution/{simple_ring_async_v1,async_profile_v1}_spec.spl`, `test/01_unit/lib/nogc_async_mut/async_ring/{simple_ring,mission_adapter}_spec.spl`, and `test/01_unit/lib/nogc_async_mut_noalloc/async/{async_trace_ring,mission_ready_set}_spec.spl`; contracts, profiles, transitions, mission admission, exact mission wake, traces |
| I | Integration | `test/02_integration/lib/async/simple_ring_async_base_integration_spec.spl`, `simple_ring_profile_integration_spec.spl`, and `simple_ring_future_compat_spec.spl`; typed rings, full five-profile/provider matrix, explicit nonblocking Future adapter, exact wake |
| C | Concurrency | `test/02_integration/lib/async/simple_ring_async_base_concurrency_spec.spl`; owner transfer, races, ABA/reset, fairness and independent progress |
| S | System/manual | `test/03_system/runtime/simple_ring_async_base_spec.spl`; all selected requirements through the real software-provider surface |
| P | Performance | `test/05_perf/runtime/simple_ring_async_base_perf_spec.spl`; O(1), allocation/blocking, latency distributions and bounded-resource receipts |
| F | Bounded model | `test/00_formal_verification/runtime/simple_ring_async_base_bounded_model_spec.spl` and `doc/09_report/evidence/simple_ring_async_base_concurrency_linearization_2026-08-26.md`; exhaustive capacity-one length-six traces and explicit non-proof boundaries |

The SSpec uses these exact manual-facing calls, in this order, with literal
`step("...")` expressions:

1. `Configure the async execution profile`
2. `Reserve and commit bounded ring work`
3. `Complete work and wake the exact task`
4. `Reject stale, duplicate, and over-capacity activity`
5. `Prove mission bounds and deterministic policy`
6. `Verify bounded nonfunctional ring behavior`
7. `Verify portable provider and compatibility facts`

Reusable setup/checker names are frozen as
`setup_simple_ring_profile_fixture` and `check_simple_ring_invariants`.
Displayed scenarios call the setup/checker; reusable setup is folded with
`@inline`/`@prev` in generated documentation. Any temporary helper must fail
with `assert(false)` or `fail(...)`, never a placeholder pass.

## Traceability matrix

Every row requires all five evidence classes for Phase 3 qualification. Phase 2
requires the corresponding source fixture and honest diagnostic status. Case
labels are stable identifiers for the eventual specs and must remain visible in
the manual or folded source.

| ID | Unit (U) | Integration (I) | System/manual (S) | Performance (P) | Concurrency (C) |
|---|---|---|---|---|---|
| REQ-SRA-001 | U-01 typed capacity/full/empty | I-01 typed SQ/CQ provider | S-01 bounded admission | P-01 O(1) reserve/take | C-01 single-owner capacity |
| REQ-SRA-002 | U-02 token/slot/generation | I-02 lookup/foreign token | S-04 stale rejection | P-02 reuse overhead | C-02 ABA/reset race |
| REQ-SRA-003 | U-03 reserve/release/batch policy | I-03 partial batch receipt | S-02 reserve/commit | P-03 batch O(batch) | C-03 commit linearization |
| REQ-SRA-004 | U-04 terminal state matrix | I-04 provider completion | S-03 exactly-one terminal | P-04 completion latency | C-04 duplicate terminal race |
| REQ-SRA-005 | U-05 cancel/reset outcomes | I-05 cancelled provider work | S-04 stale/reset denial | P-05 cancellation cost | C-05 cancel-vs-complete order |
| REQ-SRA-006 | U-06 owner/payload transitions | I-06 registered payload adapter | S-02 ownership receipt | P-06 no hot-path copy/alloc | C-06 cross-owner transfer |
| REQ-SRA-007 | U-07 exact wake key | I-07 wake queue integration | S-03 targeted wake | P-07 no task scan | C-07 wake fairness |
| REQ-SRA-008 | U-08 frame/context/poll result | I-08 pending/ready provider | S-01 nonblocking poll | P-08 sync-leaf overhead | C-08 independent pending task |
| REQ-SRA-009 | U-09 metadata/supervisor policy | I-09 parent cancellation | S-05 structured metadata | P-09 frame bounds | C-09 parent/child cancellation |
| REQ-SRA-010 | U-10 mapping grades/admission | I-10 provider grade matrix | S-01 explicit fallback | P-10 mapping overhead | C-10 deterministic provider choice |
| REQ-SRA-011 | U-11 software provider lifecycle | I-11 end-to-end submit/take/complete | S-02..S-04 reference flow | P-11 bounded provider | C-11 provider owner progress |
| REQ-SRA-012 | U-12 five profile constructors | I-12 profile/provider admission | S-01 and S-05 profile matrix | P-12 profile costs | C-12 deterministic profiles |
| REQ-SRA-013 | U-13 mission_alloc validation | I-13 sealed arena admission | S-05 arena bounds | P-13 no growth after admission | C-13 arena ownership |
| REQ-SRA-014 | U-14 mission_pool validation | I-14 fixed pool lifecycle | S-05 pool policy | P-14 pool high-water | C-14 no stealing/detach |
| REQ-SRA-015 | U-15 fingerprint identity/change | I-15 configuration round-trip | S-01 fingerprint receipt | P-15 fingerprint cost | C-15 stable admission identity |
| REQ-SRA-016 | U-16 adapter error/fallback facts | I-16 compatibility adapter | S-04 migration denial cases | P-16 adapter overhead | C-16 adapter ownership |
| REQ-SRA-017 | U-17 bounded counters/events | I-17 telemetry receipt | S-03 observability | P-17 p50/p99/p99.9 telemetry | C-17 trace-ring ownership |
| REQ-SRA-018 | U-18 effect/lowering declarations | I-18 extension-point validation | S-05 explicit V1 exclusions | P-18 no implicit-lowering claim | C-18 effect policy determinism |
| NFR-SRA-001 | U-N01 operation classes | I-N01 batch/provider calls | S-N01 bounded exact-slot path | P-N01 O(1)/O(batch) | C-N01 no global scan |
| NFR-SRA-002 | U-N02 finite capacities | I-N02 allocation detector | S-N02 resource envelope | P-N02 RSS/pool high-water | C-N02 bounded ownership |
| NFR-SRA-003 | U-N03 nonblocking state | I-N03 provider/compat poll path | S-N03 adapter reports no block/scheduler | P-N03 zero blocking calls | C-N03 progress while pending |
| NFR-SRA-004 | U-N04 deterministic policy | I-N04 overload/fallback | S-N04 deterministic receipt | P-N04 repeatability | C-N04 schedule/rejection order |
| NFR-SRA-005 | U-N05 wrap/reuse states | I-N05 delayed completion | S-N05 reset receipt | P-N05 race overhead | C-N05 ABA/cancel race |
| NFR-SRA-006 | U-N06 evidence schema | I-N06 evidence aggregation | S-N06 blocked-until-complete | P-N06 fingerprinted receipts | C-N06 proof inputs/owners |
| NFR-SRA-007 | U-N07 branch inventory | I-N07 boundary matrix | S-N07 requirement scorecard | P-N07 coverage and workload | C-N07 all interleavings in scope |
| NFR-SRA-008 | U-N08 metric schema | I-N08 representative fixture | S-N08 before/after receipt | P-N08 p50/p99/p99.9/RSS | C-N08 wake/overload metrics |
| NFR-SRA-009 | U-N09 sync leaf | I-N09 direct leaf path | S-N09 no frame/ring | P-N09 allocation regression | C-N09 leaf independent progress |
| NFR-SRA-010 | U-N10 mapping portability | I-N10 five-profile grade/fallback matrix | S-N10 explicit software mapping/fallback | P-N10 mapping comparison | C-N10 provider ownership |
| NFR-SRA-011 | U-N11 adapter preservation | I-N11 compatibility path | S-N11 exact-token nonblocking compatibility | P-N11 adapter delta | C-N11 backpressure preserved |
| NFR-SRA-012 | U-N12 artifact links | I-N12 mirrored manual inputs | S-N12 operator workflow | P-N12 retained provenance | C-N12 owner/reviewer receipt |

## Required assertions and depth

Each REQ scenario has at least happy, boundary, and rejection/error assertions
using only canonical matchers (`to_equal`, `to_be`, `to_be_nil`, `to_contain`,
`to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`). Unit
coverage must include every constructor, state transition, full/empty result,
generation wrap/reuse, duplicate terminal, cancellation/reset ordering, batch
policy, profile validation branch, and fingerprint-change branch. The owned
implementation files must reach at least 80% branch coverage; uncovered
branches are a FAIL or a tracked bug with file:line and unblock condition.

Concurrency evidence must show single-owner mutation and explicit transfer,
stale/ABA rejection, cancellation-versus-completion linearization, reset
invalidation, exact wake targeting, independent-task progress, bounded overload,
and the declared fairness/non-starvation scope. One interleaving is not formal
proof. Formal or mission claims require the effect report, suspension map, task
topology/max-concurrency, ring-depth and memory bounds, blocking proof,
priority/deadline map, cancellation map, provider/fallback report, and matching
configuration/artifact fingerprints. In their absence the result is BLOCKED,
not PASS; this V1 plan makes no theorem or model-checking claim.

## Execution order and exact commands

The authoritative per-NFR executable routing is also stored in the
`nfr_acceptance` table of `.spipe/simple-ring-async-base/todo.sdn`. All twelve
NFRs have a named test or gate; rows requiring measurements, coverage, compiler
proof, or generated provenance remain TODO until those receipts exist.

Run once on the final changed state, retaining logs and receipts under
`build/test-artifacts/simple_ring_async_base/`:

```text
SIMPLE_LIB=src bin/simple check src/lib test/01_unit/lib/common/contracts/execution/simple_ring_async_v1_spec.spl test/01_unit/lib/common/contracts/execution/async_profile_v1_spec.spl test/01_unit/lib/nogc_async_mut/async_ring/simple_ring_spec.spl test/01_unit/lib/nogc_async_mut/async_ring/mission_adapter_spec.spl test/01_unit/lib/nogc_async_mut_noalloc/async/async_trace_ring_spec.spl test/01_unit/lib/nogc_async_mut_noalloc/async/mission_ready_set_spec.spl test/02_integration/lib/async/simple_ring_async_base_integration_spec.spl test/02_integration/lib/async/simple_ring_profile_integration_spec.spl test/02_integration/lib/async/simple_ring_future_compat_spec.spl test/02_integration/lib/async/simple_ring_async_base_concurrency_spec.spl test/00_formal_verification/runtime/simple_ring_async_base_bounded_model_spec.spl test/03_system/runtime/simple_ring_async_base_spec.spl
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/01_unit/lib/common/contracts/execution/simple_ring_async_v1_spec.spl --mode=native
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/01_unit/lib/common/contracts/execution/async_profile_v1_spec.spl --mode=native
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/01_unit/lib/nogc_async_mut/async_ring/simple_ring_spec.spl --mode=native
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/01_unit/lib/nogc_async_mut/async_ring/mission_adapter_spec.spl --mode=native
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/01_unit/lib/nogc_async_mut_noalloc/async/async_trace_ring_spec.spl --mode=native
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/01_unit/lib/nogc_async_mut_noalloc/async/mission_ready_set_spec.spl --mode=native
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/02_integration/lib/async/simple_ring_async_base_integration_spec.spl --mode=native
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/02_integration/lib/async/simple_ring_profile_integration_spec.spl --mode=native
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/02_integration/lib/async/simple_ring_future_compat_spec.spl --mode=native
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/02_integration/lib/async/simple_ring_async_base_concurrency_spec.spl --mode=native
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/00_formal_verification/runtime/simple_ring_async_base_bounded_model_spec.spl --mode=native
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/03_system/runtime/simple_ring_async_base_spec.spl --mode=native
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/05_perf/runtime/simple_ring_async_base_perf_spec.spl --mode=native
bin/simple spipe-docgen test/03_system/runtime/simple_ring_async_base_spec.spl --output doc/06_spec --no-index
bin/simple sspec-maintain scan test/03_system/runtime/simple_ring_async_base_spec.spl
find doc/06_spec -name '*_spec.spl' | wc -l
sh scripts/audit/direct-env-runtime-guard.shs --working
sh scripts/audit/direct-env-runtime-guard.shs --staged
```

The system command is accepted only with real assertions, a complete mirror,
docgen `0 stubs`, and zero executable specs under `doc/06_spec`. Performance
acceptance retains before/after p50, p99, p99.9, throughput, occupancy,
high-water/full events, batch/kick counts, poll/suspend/wake latency, and RSS
or pool/arena high-water. Any unmet target is a concrete tracked bug, never a
softened assertion. The generated manual must be understandable without the
SSpec source and must show the five frozen steps, scope/exclusions, scorecard,
evidence paths, and limitations.

## Environment, risks, and exclusions

Use the pure-Simple `bin/simple` runtime with no seed or hosted fallback. The
fixture must be deterministic, self-contained, and use the bounded software
provider; OS/device queues, native io_uring, full compiler lowering, and all
downstream migrations remain excluded. Primary risks are hidden allocation in
completion/wake paths, global task scans, stale generation acceptance, duplicate
terminal publication, profile combinations that silently weaken mission policy,
and performance claims based on a single warm run. Repeatability and retained
receipts are required before any PASS.
