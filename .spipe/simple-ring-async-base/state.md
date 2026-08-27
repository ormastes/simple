# Feature: Simple Ring and Async Base

## Raw Request

`$sp_dev make design refactoring and plan doc or updates. make simple ring base and async base. with profiles. and excessive tests. go pherallel with doc/01_research/runtime/simple_ring_first_async_first_architecture_2026-08-26.md`

## Task Type

feature

## Refined Goal

Establish a pure-Simple, profile-aware `SimpleRing` and stackless async-task foundation that implements the selected ring-first architecture, supplies explicit bounded semantics for common/server/embedded/mission profiles, and is supported by comprehensive executable evidence and current architecture, design, plan, guide, and expert documentation.

Phase decision (user, 2026-08-26): Phase 2 accepts the pure-Simple foundation;
qualification tests and receipts that require the deployed self-host or
compiler/linker evidence move to the Phase 3 TODO database.

## Acceptance Criteria

Phase 2 acceptance: AC-1 through AC-6, AC-9, and AC-13 through AC-15 at
source/design/diagnostic scope. Phase 3 qualification: AC-7, AC-8 quantitative
coverage, AC-10 generated-manual execution, AC-11, AC-12 universal proof
obligations, and AC-16. Phase 3 rows are tracked in `todo.sdn`; they are not
silently treated as Phase 2 PASS.

- AC-1: Final feature and NFR requirement documents trace every selected base-layer rule from the research document, including typed SQ/CQ contracts, exact terminal completion, generation-safe tokens, explicit backpressure, cancellation/reset outcomes, targeted wakeup, bounded storage, provider mapping grades, and profile fingerprints; no unresolved `*_options.md` remains for this lane.
- AC-2: Architecture and detail-design documents define one public ring/task model, MDSOC ownership boundaries, provider/executor extension points, error behavior, migration adapters, and explicit exclusions for later platform migrations; the design contains no competing Future or scheduler ABI.
- AC-3: The public base uses the shared names `SimpleRing<Op, Cpl>`, `RingToken`, `RingGeneration`, `RingAdmission`, `RingCompletion`, `RingMappingGrade`, `AsyncTaskFrame`, `TaskPollResult`, `TaskContext`, and `AsyncProfile`; implementation is pure Simple unless evidence proves a missing owner-boundary runtime capability.
- AC-4: `SimpleRing` provides bounded reserve/commit/complete/cancel/reset behavior with O(1) queue operations, explicit full/empty results, slot-plus-generation stale-completion rejection, exactly one terminal completion for each admitted single-shot operation, batched admission, occupancy/high-water telemetry, and no silent allocation or growth after construction.
- AC-5: The async base provides stackless `poll(frame, context) -> Ready(result) | Pending(wait_token)` semantics, exact task wake keys, parent/cancellation metadata, and forbids an executor from blocking while polling; compatibility adapters may exist but cannot introduce a second task model.
- AC-6: Profiles named `common`, `script`, `server`, `mission_alloc`, and `mission_pool` define async surface/policy, scheduler, memory, ring-mapping, assurance, instrumentation, placement, capacity, blocking, allocation, detachment, fallback, and determinism policies; invalid combinations fail closed and each profile produces a stable fingerprint.
- AC-7: `mission_alloc` proves bounded admitted arenas and no hot-path growth, while `mission_pool` proves fixed/static task, descriptor, buffer, timer, join/cancellation, and trace capacities with no work stealing or detached work; both retain bounded async, cancellation, deadlines, and device-ring support.
- AC-8: Unit tests cover every constructor, state transition, boundary, error, wraparound/generation case, duplicate terminal attempt, cancellation/reset race ordering, full/empty condition, batch partial/failure policy, profile validation branch, and fingerprint stability branch with at least 80% branch coverage for owned implementation files.
- AC-9: Integration tests exercise multiple typed operation/completion pairs, software-provider submission/completion, targeted wakeup without global scanning, independent tasks making progress while another is pending, compatibility adaptation, profile/provider admission, and deterministic overload behavior.
- AC-10: Modern SSpec system scenarios trace all requirements and use the frozen manual-facing steps `Configure the async execution profile`, `Reserve and commit bounded ring work`, `Complete work and wake the exact task`, `Reject stale, duplicate, and over-capacity activity`, and `Prove mission bounds and deterministic policy`; setup/checker helpers are `setup_simple_ring_profile_fixture` and `check_simple_ring_invariants`, and any temporary implementation fails explicitly with `assert(false)` or `fail(...)`.
- AC-11: Performance evidence establishes O(1) queue/task operations, zero steady-state hot-path allocation for server and mission profiles, zero blocking calls from poll/executor/ring completion paths, no task-count scan after completion, and measured before/after p50/p99/p99.9 plus high-water/full-event data on representative fixtures; any unmet target becomes a concrete tracked bug with file:line and unblock condition.
- AC-12: Concurrency/resource evidence covers single-owner mutation, cross-owner transfer boundaries, ABA/stale generation rejection, cancellation-versus-completion linearization, reset invalidation, fairness/non-starvation scope, and bounded-resource proofs; a single interleaving test is not accepted as formal proof.
- AC-13: The system test plan, agent task plan, mirrored `doc/06_spec` manual, and operator/developer guide name the exact focused commands and evidence owners; the manual is understandable without opening the SSpec source and `doc/06_spec` contains no executable `*_spec.spl` files.
- AC-14: Runtime-concurrency public API documentation remains accurate in `doc/07_guide/lib/misc/stdlib.md`, `doc/07_guide/compiler/check_perf.md`, and `.codex/skills/coding/SKILL.md`, distinguishing OS threads, cooperative green tasks, bounded-worker multicore tasks, and the new ring/task foundation without advertising unavailable M:N or provider capability.
- AC-15: Knowledge updates cover research, requirements, architecture, design, plans, `doc/07_guide`, `doc/00_llm_process/feature_expert/simple_ring_async_base/skill.md`, and the applicable runtime/compiler layer-expert skill; every discovered-but-unfixed gap has a `doc/08_tracking/bug/` record with file:line and unblock condition, and any must-check v3 TODO/blocked row names an owner and actionable unblock condition (`none` for PASS).
- AC-16: Focused pure-Simple checks, lint, duplicate-check, SSpec maintenance, direct-env/runtime working and staged guards, generated-spec layout guard, and applicable compiler/lib/MCP/LSP checks pass once on the final changed state; verification reports requirement-by-requirement evidence and respects the three-cycle cap.

## Scope Exclusions

- Full migration of every host driver, Monoio, SOSIX service, SimpleOS device, NVMe firmware pipeline, web/DB server, and renderer is deferred to follow-on phases; this lane must provide their stable base contracts and compatibility seams, not falsely claim those migrations complete.
- Implicit-await grammar/HIR/MIR lowering is designed and given extension contracts here but is not implemented unless the existing compiler structure shows it is required to make the base task ABI usable without a separate compatibility model.
- Native io_uring, Vulkan, NVMe, and hardware queues are provider conformance targets; the required executable provider in this base lane is the bounded software reference provider.
- Release, version bump, tag, and push are excluded.

## Cooperative Review

- Parallel sidecars: compiler/async lowering audit; runtime/ring/provider audit; profiles/mission policy audit; tests/SPipe/manual audit; architecture/docs migration audit.
- Merge owner: primary Codex `/root`.
- Final reviewer: primary highest-capability Codex `/root`; no sidecar may accept done marks, broad exclusions, or generated-manual quality.
- Shared interfaces: `SimpleRing<Op, Cpl>`, `RingToken`, `RingGeneration`, `RingAdmission`, `RingCompletion`, `RingMappingGrade`, `AsyncTaskFrame`, `TaskPollResult`, `TaskContext`, `AsyncProfile`.
- Frozen manual steps: `Configure the async execution profile`; `Reserve and commit bounded ring work`; `Complete work and wake the exact task`; `Reject stale, duplicate, and over-capacity activity`; `Prove mission bounds and deterministic policy`.
- Setup/checker helpers: `setup_simple_ring_profile_fixture`; `check_simple_ring_invariants`.
- Fail-fast placeholder rule: all temporary scenario or provider helpers use `assert(false)` or `fail(...)`; no placeholder pass or hardcoded success.
- Generated-manual review owner: primary Codex `/root` after sidecar source/coverage audit.

## Phase

phase-2-complete

## Log

- dev: Created state file with 16 acceptance criteria (type: feature) and froze shared interface/helper vocabulary before parallel fan-out.
- research/design: Added selected requirements, NFRs, MDSOC architecture, detail design, system-test plan, agent-task plan, guides, and feature/layer expert notes; excluded platform/compiler migrations are recorded explicitly.
- implementation: Added pure contract/task types, five validated/fingerprinted profiles, the bounded single-owner hosted `SimpleRing`, explicit all-or-nothing batch admission, and the bounded software provider.
- diagnostic evidence: Contract, ring, and provider focused interpreter specs emitted complete green verdicts, but the invoked frontend identified itself as the Rust bootstrap seed; these results are diagnostic and are not final pure-Simple acceptance evidence.
- Phase 3 qualification debt: generated-manual provenance, admitted performance/resource evidence, quantitative coverage, compiler/static-placement proof, and final pure-Simple verification remain TODO; system/concurrency diagnostic fixtures already exist.
- system evidence: Added the five-flow modern SSpec and an explicitly authored (not generated-PASS) mirror. The first seed diagnostic exposed two class-field copy/optional access issues in the scenario; cycle 1 repaired them, and cycle 2 emitted `5 examples, 0 failures` with no dropped examples. The seed warning keeps this diagnostic rather than final acceptance evidence.
- open evidence: `doc/08_tracking/bug/simple_ring_async_base_open_evidence_2026-08-26.md` records the pure-Simple binary, mission-static-storage, compiler blocking-path, performance, and concurrency-proof unblock conditions.
- implementation expansion: Added typed payload leases and full operation metadata, callable stackless-task and trace contracts, explicit cancellation state, bounded provider-depth admission, caller-clock latency telemetry, hosted mission resource admission, and a fixed-capacity trace ring.
- expanded diagnostics: Profile validation/fingerprint coverage now exercises all presets and fingerprint fields; focused contract, mission-adapter, trace-ring, integration, concurrency, and system diagnostics are green under the bootstrap seed. The system scenario exhausted its three-cycle cap and must not be rerun this session.
- performance status: Added `test/05_perf/runtime/simple_ring_async_base_perf_spec.spl` and an explicitly non-PASS authored manual. Execution is blocked by the non-admitted seed and an unrelated existing `dir_list` semantic failure; no baseline/RSS/allocation claim is accepted.
- verification status: Source stub/raw-runtime scans and direct-env guards are clean for this lane. Numbered-artifact working-tree guard is blocked only by two unrelated dirty RISC-V DTB documents. Final pure-Simple checks, coverage, generated-manual provenance, static mission proof, and formal concurrency evidence remain open.
- compatibility evidence: Added `future_compat_adapter.spl`, which maps legacy nonblocking `Future.poll` to the canonical `TaskPollResult` using the exact caller-supplied admitted token and reports that it neither blocked nor created a scheduler. Its new three-example integration diagnostic passed under the bootstrap seed.
- mission ready evidence: Added scalar-only 64-slot `MissionReadySet64` with owner checks, explicit admission, O(1) exact-slot wake/claim, generation reset, and terminal quiesce. Its six-example seed diagnostic passed; compiler-placement, link-time-static, and backend-allocation-free proof remain explicitly false.
- bounded-model evidence: Exhaustively checked all 117,649 capacity-one action traces of length six and documented source linearization/resource accounting. The seed diagnostic passed 1/1; this is bounded model evidence, not universal thread-safety or refinement proof.
- terminal verification audit: Lane-scoped whitespace and noalloc-source scans pass. The same mandatory blocker has persisted for three goal turns: `bin/simple` is still the Rust bootstrap seed, so final pure-Simple checks, coverage, docgen provenance, native performance/RSS/allocation receipts, and compiler/linker placement evidence cannot be produced. No remaining local diagnostic may truthfully substitute for those gates.
- phase boundary update: Per user direction, accepted the pure-Simple source implementation as Phase 2 complete and moved self-hosted test execution, coverage, docgen, performance/resource, compiler lowering/static placement, and final qualification into `.spipe/simple-ring-async-base/todo.sdn`. This changes delivery sequencing, not the truth status of deferred evidence.
- NFR/profile test readiness: Added two modern SSpec NFR mechanism scenarios covering bounded exact-slot wake, nonblocking compatibility polling, deterministic generation-safe behavior, explicit provider mapping/fallback, and telemetry. Added a four-example integration matrix for all five profiles, provider admission/rejection, stable/distinct fingerprints, and mission fail-closed policy; its bootstrap-seed diagnostic passed 4/4. The existing measured perf spec remains the Phase 3 p50/p99/p99.9 fixture. The authored system manual is intentionally stale until the Phase 3 pure-Simple docgen row runs.
- NFR acceptance routing: Added a twelve-row `nfr_acceptance` ledger mapping every NFR to its modern SSpec, integration, concurrency/model, perf, coverage, compiler, docgen, or final verification gate. Quantified rows remain TODO rather than being inferred from mechanism tests.
