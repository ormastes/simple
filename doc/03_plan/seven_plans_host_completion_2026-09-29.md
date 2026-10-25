# Completion plan for the seven requested items, by host

## 2026-10-25 reconciliation against `release/1.0.0` (PRs #4498-#4604)

Reconciled at `origin/release/1.0.0` @ `73c4aef632a` (merge of #4600). This
section records what landed per item today and the cross-plan decisions; it
does not certify any host cell. The cache/per-file plan set that items 1, 2, 5
and 6 share is indexed, with every conflict resolved to one current answer, in
[`compiler/cache/cache_perfile_plan_index_2026-10-25.md`](compiler/cache/cache_perfile_plan_index_2026-10-25.md).
Each item's own plan/design/guide/wiki refresh lands in its own
"[seven-plan item N docs]" PR; this umbrella only links them. P-G2 #4600 (TLDR
specialization list + `.rr` producers) merged as `73c4aef632a` while this was
written; the one open follow-up is the AOP match-shard driver wiring #4401.

| Item | Landed today (release/1.0.0) | State |
|---|---|---|
| 1. Parser sharing / platform / dynload | `ParseContext` stage 1 per-owner snapshots (#4505 #4512-#4516 #4518 #4519 #4521 #4522 #4523 #4526 #4527 #4529 #4530 #4532-#4535 #4538-#4541 #4548 #4604) and stage 2 accessor indirection for parser/stmt/expr/decl (#4544 #4550 #4553 #4555 #4558 #4560 #4561 #4568); `--parse-fibers=i/n` child lane (#4508); `.spab` packed parse cache default (#4582 #4589, equality spec #4503). Stages 3-4 (context-owned storage, true in-process parallel parse) open. No dynload or SimpleOS-release landing in this range | IN_PROGRESS (parser sharing); dynload/release TODO |
| 2. SCV + jj + GitHub | Only #4574 (inventory events keep NUL-carrying text whole). Cost tracing #4492 and reader-scratch #4497 open. Cache-manager tier decision for SCV consumers: index §2 row 1 | TODO (unchanged) |
| 3. Typed DataFrame collections | nothing in range | TODO (unchanged) |
| 4. mold-based MDSOC++ linker | linker-adjacent only: mswsock default lib (#4507), COMDAT instance dedup for non-LLVM backends (#4603) | TODO (unchanged) |
| 5. Kernel/extension aspects, binary size | AOP pointcut-affected invalidation plan (#4511, `incremental_rebuild_plan_v1`); directory match-shard driver wiring #4401 still open. Provider/size work: none in range | IN_PROGRESS per 2026-10-11 note; cache part partial |
| 6. Compile optimization | per-module lowering default, whole-program behind `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` (#4525 #4547); objects streamed during MIR, batch 8 (#4566); HIR admission linear (#4557), validation blob removed (#4562), admission paths normalised once (#4552); cache scope published before shard spawn, HIR cache decoupled from `SIMPLE_FRONTEND_CACHE=0` (#4565); Stage 2 cache content-keyed (#4559); file-worker claim loop opt-in `SIMPLE_FILE_WORKERS=1` (#4576 #4584 #4585 #4588 P-A), incremental planner + object cache in the pool (P-E #4594), default-flip readiness + overlap receipt gate (P-F #4592); module-scoped mono with COMDAT, no global pass in the per-file lane (#4575 #4580 #4597 #4598 P-G3 #4603 P-D); reader-driven concrete generic instances (P-G1 #4591); cache budgets + admit-before-plan (#4506); docs/design (#4510 #4542 #4564 #4567). The true per-file lane is **not** the default (`NATIVE_PER_FILE_PIPELINE_DEFAULT_V1 = "0"`) ; evening update: P-G4..P-H merged (#4625 #4628 #4653 #4672 #4683), P-G7 #4696 open, see Progress 2026-10-25 (evening) below | IN_PROGRESS (Windows native lane); no end-to-end timing on a stage2 built from these sources yet |
| 7. Profile-switchable containers | `CollectionFeedbackState` snapshot only (#4535, parse-side state move) | TODO (unchanged) |

Cross-item decisions taken today (details and evidence in the index §2):
persisted cache tiers are packed AST + TLDR, generic instances per concrete key,
AOP weave bodies, objects, lib/bin — HIR stays in memory and there is no
general MIR cache; `.spab` is the default parse-cache format with `.fpc` as the
opt-out fallback; "per-file default" in guides means per-module lowering with
streamed objects, while the barrier-free `--file-worker` lane stays opt-in;
mono is module-scoped always inside the file-worker lane and global outside it;
shards, file workers and `--parse-fibers` children coexist, and in-process
fibers wait on `ParseContext` stages 3-4; single-flight futures replace locks
and leases (removal list still open). Item PRs whose docs still say otherwise
carry a "Superseded (2026-10-25)" note at the stale section (index §3).

Host matrix: no cell moves to VERIFIED. Today's Windows measurements
(`true_per_file_pipeline_v1.md` §1) came from a frozen stage2 that predates
every fix above, and the seed cannot interpret the current stdlib on Windows,
so Windows native evidence for item 6 is "landed + unit specs", not a host run.
Items 1 and 6 Windows-native cells become IN_PROGRESS (owners claimed, PRs
landed); every other cell is unchanged.

### Progress 2026-10-25 (evening)

PR states verified with `gh pr view` against base `release/1.0.0`.

**Per-file packages merged:** P-A #4588 `e0efb59638f`, P-B #4597 `7ec523277de`,
P-C #4589 `d1ee8738d60`, P-D #4603 `cbe361c2497`, P-E #4594 `9314979e6e6`,
P-F #4592 `1c6ccfb61c4`, P-G1 #4591 `3383735e8cb`, P-G2 #4600 `73c4aef632a`,
P-G3 #4598 `220b35b4b35`, P-G4 #4625 `7ec28192eb0`, P-G5 #4628 `963f32429a3`,
P-G5b #4653 `5de3687be0b`, P-G6 #4672 `03e6d90af24`, P-H #4683 `bf4c14a31e1`
(stage3 and plain native-build go through the file-worker pool, fail-closed).
E-MONO-040 fails closed for imported generics: #4651 `6c257d14918`.

**Open:** P-G7 #4696 (instance object producer + link wiring) is OPEN; approved by lead
reviewer (comment), pending merge. Merge release_phase3 into
release/1.0.0: #4704 OPEN.

**Default stays off:** `NATIVE_PER_FILE_PIPELINE_DEFAULT_V1 = "0"`
(`SIMPLE_FILE_WORKERS` default "0"). Flip waits on a proof run: stage3 -> stage3'
built with P-H, then a per-file self-rebuild that yields an overlap receipt
(`scripts/check/check-per-file-overlap-receipt.shs`). No such receipt exists yet.

**Stage evidence (in progress, not a retained measurement):** stage2 built cold
from `d72188e68ec` (1534 modules, 0 failed, mswsock workaround dropped). The
stage3 whole-program run is in progress with 0 MIR errors (was 3211); it is
single-threaded and CPU-bound.

**Other landings:** #4610 stale lock reclaim / orphan reaping `52ecd8b7725`;
#4622 Mach-O as conditional build tag `a269ecaecba`; #4623 pre-push gate clear
error for missing gate script `fc894af98af`; #4633 host-scaled tree RSS cap
`ae3c1307476`; #4682 llvm-mingw drive-letter admission `784ac5aa304`; seed
externs #4608 `57a129fb2b9` and #4688 `5bd6f027abb`; spec fixes #4636
`1cfdf5876ca`, #4635 `33bfd461fbb`, #4638 `4f5e0d91b88`. Also merged since the
morning: memory #4698 `574b8bb6e70` and #4705 `31bafe03f9e` (HIR / per-module MIR
eviction), perf #4693 `35fe920618d` (sha256 accelerator), MIR #4706
`a853ac75861`, stage2 #4684 `dd7cede08a3` and #4697 `7c1e83a584b`.

**Still failing / under investigation:** HIR cache selfcheck (239/1495 hits);
seed JIT fallback on `native_build_main`.
## Item 5 continuation and variation direction — 2026-10-11

The user resumed Item 5 on release and selected the integrated SIMD/GPU/SOSIX variation proposal for its plan/design. This supersedes the historical stop instruction below for Item 5 only; it does not change other items or certify any host cell.

Use the [existing Item 5 implementation plan](compiler/perf/runtime_optional_provider_binary_size_optimization_plan_2026-09-02.md#2026-10-11-selected-variation-migration) for proposal P0–P9. Preserve the immediate goals: optional AVX512/CUDA loading and small default image, real DB/webserver on/off correctness/performance, full bootstrap and ARM/RISC-V provider/application qualification. Reuse environment-variant and SOSIX owners; add target/ABI/worker/device attributes and retirement evidence to existing rows.

Current documentation baseline is release `02b150b385013d21bc408b45244431de85d391de`; the registry and cast repairs are merged there. Full Item 5 remains IN_PROGRESS/unqualified. For this expressly release-targeted lane, landing means a reviewed merged PR on `release/1.0`, not the historical main-only destination below. A live older candidate remains immutable and its results retain that older identity.

Date: 2026-09-29
Status: stopped at user request; implementation completion is not certified.
## 2026-10-02 stop checkpoint

The user stopped further feature implementation for items 1 and 5 at their
current partial scope, then requested landing completed fixes on release and
stopping this session. Neither item is implementation-complete. All session-owned
bootstrap jobs are stopped with caches and logs retained. Source fixes in
PRs #2163-#2166 landed on release/1.0; this does not establish native acceptance
or completion of the seven plans. No current coding percentage is certified.
See the [restart checkpoint](infra/bootstrap/bootstrap_restart_2026-10-01.md)
for terminal evidence, unfinished work locations and verification gaps.

Parallel pure-Simple TDD update (2026-09-29): five bounded implementation
changes and their diagnostic results are recorded in
[the progress report](evidence/seven_plans/parallel_pure_simple_tdd_2026-09-29.md).
This does not change the host certification cells below to VERIFIED or DONE.
The report separates existing implementation, new regression fixes, and the
remaining requirements; no unsupported completion percentages are assigned.

Execution update (2026-09-29): the user selected Windows first, then macOS,
and requested branch publication and PRs. This ordering supersedes the initial
Windows/Linux ordering below for this execution lane; it does not remove any
supported-host requirement. See the [Windows bootstrap investigation](evidence/seven_plans/windows/bootstrap_readiness_2026-09-29.md).

Subsequent goal update (2026-09-29): Windows first, then Linux through WSL.
This is the current execution order. The earlier macOS request remains recorded
as host scope, but macOS completion must not be inferred from either lane.

## Scope and ownership

Complete the seven items listed below on each supported host. This means seven
distinct feature plans, not seven repeated test runs. Implement shared code once;
verify each host and target combination separately.

Windows native and Linux/WSL are the first execution lanes. macOS, standalone
Linux, FreeBSD, and additional supported hosts remain explicit TODO lanes until
their evidence is available. SimpleOS is a target/guest lane, not evidence that
the development host itself works. Add architecture-specific rows when support
is claimed; an x86_64 result does not certify ARM64 or other architectures.

The execution owner claims one host/item task in the TODO database before editing.
The merge owner integrates shared changes; the final reviewer checks requirements,
host evidence, and the landed commit. Sidecar agents: N/A for this planning change.
Preserve other sessions' work and existing research. Use isolated worktrees when
implementation lanes overlap.

## Status rules

- TODO: work or current host verification remains.
- IN_PROGRESS: an owner has claimed a concrete task.
- BLOCKED: record the exact failing command, cause, next action, and owner.
- VERIFIED: required checks passed for a recorded source commit on this host.
- DONE: verified implementation has landed on main; evidence covers the landed
  content, generated manuals are current, and no required requirement remains open.
- N/A: permitted only for a documented unsupported capability with an accepted
  scope decision. Missing runners, hardware, or tests are BLOCKED, not N/A.

An open PR, a design document, source inspection, or a passing helper test alone
does not establish DONE. Windows and WSL evidence must be kept separate.

## Host tracking matrix

All cells start TODO for completion certification, even where implementation
already exists. This is not a claim that each feature is unimplemented.

| Item | Windows native | Linux/WSL | Linux native | macOS | FreeBSD | SimpleOS guest/target |
|---|---|---|---|---|---|---|
| 1. Platform unification, parser, dynload, release | IN_PROGRESS (parser sharing, 2026-10-25) | TODO | TODO | TODO | TODO | TODO |
| 2. SCV + jj + GitHub textual databases | TODO | TODO | TODO | TODO | TODO | TODO: scope admission |
| 3. Typed DataFrame collections and optimizer | TODO | TODO | TODO | TODO | TODO | TODO |
| 4. mold-based MDSOC++ linker | TODO | TODO | TODO | TODO | TODO | TODO |
| 5. Kernel/extension aspects and binary size | TODO | TODO | TODO | TODO | TODO | TODO |
| 6. Compile optimization | IN_PROGRESS (2026-10-25, no host run) | TODO | TODO | TODO | TODO | TODO |
| 7. Profile-based switchable container algorithms | TODO | TODO | TODO | TODO | TODO | TODO |

For additional hosts, create all seven child tasks when that host enters the
supported matrix. Unsupported OS/object-format combinations need an explicit
capability contract and deterministic diagnostic before scope can be closed.

## 1. Platform unification, parser sharing, environment-optimized dynload, SimpleOS release

Requested plan: **Simple Platform Unification, Parser Sharing,
Environment-Optimized Dynload, and SimpleOS Release Architecture**.

Related references:
[runtime unification](../01_research/runtime/sosix_unification/simple_sosix_runtime_unification_design_plan_2026-09-05.md),
[dynload architecture](../04_architecture/compiler/environment_optimized_dynamic_libraries.md),
[dynload plan](compiler/environment_optimized_dynamic_libraries.md).

2026-10-25: shared parser ownership is being made re-entrant through
[`parse_context_per_context_state.md`](../05_design/compiler/frontend/parse_context_per_context_state.md)
(stages 1-2 landed, see the reconciliation table; stages 3-4 open) — the
prerequisite for in-process parallel parsing shared by the compiler, LSP, lint
and the test runner. The packed `.spab` parse cache (default since #4582) is the
shared AST artifact those consumers map; LSP/lint are not wired to it yet.

- Locate the canonical umbrella document and map every retained requirement to
  implementation, tests, and host capability; retain its title/path in evidence.
- Complete shared parser ownership and check compiler/interpreter/tooling syntax
  parity. Platform adapters must expose documented capability differences.
- Complete target/CPU/environment selection, ABI validation, deterministic fallback,
  missing-library errors, and cache invalidation for dynamic loading.
- Build immutable release candidates with manifests identifying compiler, runtime,
  target, and optional providers; execute the release/bootstrap path for each host.
- Verify equivalent parser fixtures across supported execution paths, load a valid
  provider, reject incompatible providers, and boot the claimed SimpleOS target.

Done gate: requirement traceability, host parser/runtime tests, dynamic-provider
tests, and reproducible release/boot evidence all pass.

## 2. Simple distributed textual databases: SCV + jj + GitHub

References: [research](../01_research/app/tools/scv/simple_distributed_textual_databases_scv_jj_github_2026-09-13.md),
[architecture](../04_architecture/simple_distributed_textual_databases.md),
[system test plan](sys_test/simple_distributed_textual_databases.md).

2026-10-03: [concrete 51-row acceptance matrix](evidence/seven_plans/item2_acceptance_matrix_2026-10-03.md)
and [isolated development/evidence report](evidence/seven_plans/item2_dev_execution_2026-10-03.md).
Research/design and a bounded Git history-readback candidate are updated. Full
acceptance remains incomplete: no executed self-hosted RED/GREEN evidence, 153
broad fail-fast scenarios, and open durable/host/provider/performance gates.

2026-10-25 (cache part): SCV's change-preview and reverse-reference consumers
read the same `.rr` / TLDR projections the compiler publishes; the `.rr`
producers landed as P-G2 (#4600, `73c4aef632a`), and the persisted-tier decision SCV must
follow (no general MIR tier, packed AST + TLDR as the shared artifacts) is
index §2 row 1. No SCV acceptance landed in #4498-#4604.

- Finish schema validation, stable record identity, deterministic serialization,
  indexing/query behavior, and transactional local updates.
- Complete SCV integration with jj history and GitHub synchronization using the
  documented conflict and credential boundaries.
- Exercise two isolated clones: independent edits, conflicting edits, resolution,
  offline changes, interrupted synchronization, retry, and recovery without loss.
- Verify host-specific paths, case sensitivity, Unicode, line endings, file locks,
  and atomic replacement. Use a designated test remote for synchronization tests.

Done gate: convergence and recovery assertions pass with actual database contents
and history inspected; remote authorization and secrets remain outside artifacts.

## 3. Simple Typed DataFrame-able Collections and Query Optimizer

References: [collection plan IR](../01_research/compiler/collection_planner/collection_plan_ir_2026-07-31.md),
[system test plan](sys_test/collection_planner.md).

2026-10-03 development follow-up: the selected scope remains REQ-001–011 and
NFR-001–007. See the refreshed [local research](../01_research/local/collection_planner.md),
[domain research](../01_research/domain/collection_planner.md),
[architecture](../04_architecture/collection_planner.md),
[detail design](../05_design/collection_planner.md), and
[parallel ownership plan](agent_tasks/collection_planner.md).
The system test plan enumerates concrete CP-001-A through CP-011-C acceptance
cases. CP-GUARD scenarios exercise the advisory selector and its explanation;
they do not establish production lowering, backend parity, or performance.
Host completion remains TODO until those separate execution gates pass.

- Audit and close the research P0 semantic prerequisites before enabling optimized
  execution: array-map resolution, closure ABI, any/all, native Dict insertion,
  and collection behavior across backends.
- Complete typed collection/query extraction, physical-plan selection, and actual
  lowering; verify each retained filter, projection, grouping, aggregation, and
  join requirement against the reference execution path.
- Preserve ordering, duplicates, null/optional values, ownership, and error behavior
  wherever the language contract requires them.
- Measure representative cardinalities and skew; expose selected plans and reasons
  so a test proves which implementation ran.

Done gate: semantic equivalence, real lowered-plan execution, and retained NFR
targets pass on every claimed backend/host. An advisory planner alone is incomplete.

## 4. Simple Linker: mold-Based MDSOC++ Architecture and Implementation Plan

Reference: [linker research and plan](../01_research/compiler/linker/mold_mdsocpp_linker_2026-09-15.md).

- Map the retained MDSOC++ linker layers to implemented owners and interfaces.
- Complete symbol resolution, relocations, archives, dead stripping, dynamic
  dependencies, diagnostics, and deterministic output required by the plan.
- Record object-format/backend support explicitly: ELF, PE/COFF, and Mach-O must
  each have an admitted implementation or an accepted unsupported scope decision.
  Do not infer Windows/macOS support from a successful ELF/mold invocation.
- Test small fixtures through executable startup, missing/duplicate symbols,
  relocation failures, shared libraries, and stripped output.
- Link and execute the self-hosted compiler and representative applications;
  record link time, peak memory, output size, and correctness against a baseline.

Done gate: executable outputs and diagnostics meet each admitted target contract,
with real linker integration and the plan's performance requirements verified.

## 5. Kernel/extension aspect dynload for Simple size

2026-10-02: [concrete acceptance/TDD plan](sys_test/item5_provider_size_acceptance_2026-10-02.md)
and [current development evidence](evidence/item5_tdd_progress_2026-10-02.md)
retain the complete item 5 scope. Member-authority regression tests and a fix
are authored but not runtime-verified; host certification cells remain TODO.

Related references: [optional provider size architecture](../04_architecture/compiler/perf/runtime_optional_provider_binary_size_optimization.md),
[executable size architecture](../04_architecture/compiler/optimization/executable_size_reduction.md).

2026-10-25 (cache part): static-aspect incremental rebuild is planned as the
"aspect-affected pointcut set" rule (`incremental_rebuild_plan_v1`, #4511) over
directory match shards per
[`generic_aop_macro_semantic_cache_plan_2026-10-24.md`](compiler/cache/generic_aop_macro_semantic_cache_plan_2026-10-24.md) §5;
the forward-weave driver wiring (#4401) is still open, so AOP weave bodies are a
declared cache tier (index §2 row 1) without a landed producer.

- Identify the canonical kernel/extension aspect requirements and map mandatory
  core functionality versus optional providers and their dependency closures.
- Complete aspect selection, optional-provider packaging/loading, ABI checks,
  failure handling, and target capability manifests.
- Verify minimal programs exclude unused extensions using binary sections,
  symbols, and dependency manifests; verify enabling an extension restores behavior.
- Measure stripped/unstripped size and startup/RSS for minimal and representative
  applications using the same compiler, target, and build mode.
- Exercise missing/incompatible extension failures and supported lifetime behavior.
  Respect kernel/driver layering; do not introduce MDSOC+/ECS there by default.

Done gate: actual dependency exclusion and extension functionality are demonstrated,
and the retained size budgets pass without correctness regressions.

## 6. Simple compile optimization: final research, architecture, implementation plan

Related reference: [persistent package/module index](../04_architecture/compiler/perf/persistent_package_module_index_compile_optimization.md).

2026-10-25: execution authority is
[`compiler/phase3_incremental_build_completion_2026-10-13.md`](compiler/phase3_incremental_build_completion_2026-10-13.md);
design authority is
[`src_based_tldr_build_v1.md`](../05_design/compiler/incremental_build/src_based_tldr_build_v1.md)
with [`true_per_file_pipeline_v1.md`](../05_design/compiler/incremental_build/true_per_file_pipeline_v1.md)
as its per-file execution contract; the full plan set and conflict table is
[`compiler/cache/cache_perfile_plan_index_2026-10-25.md`](compiler/cache/cache_perfile_plan_index_2026-10-25.md).
Landed packages are listed in the reconciliation table above. The "clean /
warm / no-op / single-module-edit" baselines required below still do not exist
on a stage2 built from these sources; `scripts/check/check-per-file-overlap-receipt.shs`
(P-F #4592) is the acceptance proof for "no phase barrier" once that stage2 runs.

- Locate the canonical final plan and build a requirement-to-stage inventory;
  the related index document is not a substitute for the full requested scope.
- Establish clean build, warm build, no-op rebuild, and single-module-edit baselines
  with source/toolchain hashes, fixture sizes, timing, and peak RSS.
- Complete retained indexing, caching, dependency tracking, and invalidation work.
  Measure parse/type/lowering/codegen/link stages to identify remaining costs.
- Verify semantic invalidation after imports, configuration, target, compiler,
  generated files, and public interfaces change; test corrupt-cache recovery.
- Confirm optimized builds produce behavior equivalent to uncached builds and
  pass bootstrap, core runtime, MCP, and LSP requirements where affected.

Done gate: retained end-to-end compile-time and memory targets pass, cache
correctness is demonstrated, and no required optimization remains advisory only.

## 7. Profile-based, switchable container algorithms

References: [architecture and implementation status](../04_architecture/compiler/profile_switchable_container_algorithms.md),
[system test plan](sys_test/profile_switchable_container_algorithms.md),
[agent tasks](agent_tasks/profile_switchable_container_algorithms.md),
[P6 research](../01_research/compiler/collection_planner/collection_plan_ir_2026-07-31.md).

Planning snapshot: the current architecture reports adaptive set/map implementations,
attribute parsing, collection profile capture/admission, and an advisory selector.
It also records missing execution proof, typed extraction/lowering work, broader
metrics, generic coverage, and cross-backend evidence. Reconcile these statements
against the claimed source commit; do not reuse the earlier blanket conclusion
that no attribute or profile implementation exists.

- Prove each container's attribute selects the actual representation/algorithm;
  two instances with different attributes must remain independent.
- Finish supported generic set/map coverage, typed site identity, CollectionPlan
  extraction, semantic/target guards, and optimizer-to-MIR lowering.
- Complete applicable P6 workload measurements and their consumption. Distinguish
  collection feedback from unrelated function-hotspot .sprof counters.
- Execute a two-run scenario: collect workload A, save/admit its profile, then run
  the same attributed program using feedback and observe the selected algorithm.
- Repeat with a different admitted workload profile B whose measured characteristics
  justify a different choice. Check identical logical results and explain selection.
- Reject stale source/schema/target or mismatched workload identity; verify explicit
  attribute precedence, auto fallback, atomic publication, and append failure safety.
- Test representation transitions, collision-heavy input, ownership/iteration
  contracts, bounded policies, concurrent capture boundaries, and instrumentation cost.

Done gate: native Windows and Linux/WSL each demonstrate attribute -> measurement
-> profile -> guarded selection -> actual execution, with generic correctness and
retained NFRs. Parser rewrites or a selector unit test alone cannot close this item.

## Execution order and host-specific checks

1. Register seven parent tasks and host/item children; claim owners and reconcile
   existing artifacts, PRs, TODOs, and source state before changing implementations.
2. Establish an admitted pure-Simple self-hosted runner on Windows and Linux/WSL.
   Rust seeds are bootstrap-only. Record bootstrap failures as blockers.
3. Close item 1 foundations, item 3 P0 prerequisites, and item 4 linker support;
   then integrate item 5 and item 6 against those contracts. Item 2 can proceed
   independently. Finish item 7 lowering after item 3 readiness gates pass.
4. Finish and verify shared code plus Windows and Linux/WSL adapters. Keep evidence
   separate even when both hosts execute the same test suite.
5. Run remaining host tasks using the same requirement IDs and fixtures. macOS
   checks Mach-O/dylib behavior and supported architectures; Windows checks PE/DLL,
   paths, locks, and command shells; Linux checks ELF/shared libraries and filesystem
   semantics. A WSL run does not certify native Linux-specific integration.
6. For FreeBSD from Linux, use `sh scripts/check/check-freebsd-bootstrap-qemu.shs
   --smoke`, then the required `--full` pass. Preserve guest logs and target identity.
7. Review evidence, land verified changes through PRs, and update only the host/item
   tasks whose required scope is complete. Publish releases only after verify PASS.

## TODO database and evidence contract

This document does not itself insert or close database records. The execution
owner must use the repository's canonical TODO interface, reuse existing records,
and link the resulting IDs here or in a companion receipt. Do not invent task IDs.

Each host/item record must include:

- Item number, host/architecture, target triple, owner, state, and dependencies.
- Canonical plan and retained requirement IDs, implementation paths, spec paths,
  generated manual paths, and measurable NFR targets from approved requirements.
- Source commit, runtime provenance, commands, exit codes, logs, fixture identity,
  baseline/results, limitations, blocker/next action, and PR/landed commit.

Store per-host execution reports under
`doc/03_plan/evidence/seven_plans/<host>/<item>/` and bulky run artifacts under
`build/test-artifacts/seven_plans/<host>/<item>/`. These are planned paths.
Require durable CI/artifact links for evidence referenced after local cleanup.

## Verification and stopping rules

Apply the repository verification gates for the changed scope: real SPipe
assertions, requirements traceability, current generated manuals, no stubs, env
facade guards, and zero executable `_spec.spl` files in `doc/06_spec`.
Compiler/core/lib or MCP/LSP changes require the mandated compiler/lib/MCP/LSP
checks, interpreter stdio integration, and affected runtime/native/package smokes.
Record exact commands using the admitted host runtime; do not substitute the seed.

Run each acceptance check once for the implementation under review. Re-run only
when a relevant change invalidates its evidence or a required gate demands it.
After three fix/verify cycles, report the remaining blocker and stop that lane.
Never mark missing host evidence as a pass. The seven-item program is complete
only when every required host/item cell is DONE or has an accepted scope exclusion.
