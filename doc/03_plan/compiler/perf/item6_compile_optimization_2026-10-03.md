# Item 6 compile optimization: research, design, and TDD execution

Status: IN PROGRESS. This is the execution umbrella for item 6 of
`doc/03_plan/seven_plans_host_completion_2026-09-29.md`, not a completion claim.
Inspected release baseline: `7d16ab11d2227cbe5f29dc998b76a1eff326abbb`.

## Scope authority

Retain the full item 6 contract: source and toolchain identity; clean, warm,
no-op, and single-module-edit measurements; indexing, cache admission,
dependency tracking and semantic invalidation; corrupt-cache recovery;
behavioral equivalence; and bootstrap/core/MCP/LSP qualification. The persistent
package index is one implementation component, not a substitute for this scope.

The existing `PSI-REQ-001` through `PSI-REQ-007` and `PSI-NFR-001` through
`PSI-NFR-004` remain the package-index acceptance authority. Applicable cache
contracts and budgets are retained from
`doc/02_requirements/feature/compiler_semantic_cache_daemon_virtual_summary.md`
and its NFR companion. Shared frontend/hot-path constraints come from
`doc/02_requirements/feature/simple_compiler_performance_memory_efficiency.md`.
The entire optimizer transformation program is not silently relabeled item 6.
Any new requirements or relaxed budgets require user selection.

## Artifact map

| Artifact | Repository path |
|---|---|
| Current local research | `doc/01_research/local/item6_compile_optimization_2026-10-03.md` |
| Domain research | `doc/01_research/domain/item6_compile_optimization_2026-10-03.md` |
| Component implementation plan | `doc/03_plan/compiler/perf/persistent_package_module_index_compile_optimization_plan_2026-09-02.md` |
| Architecture | `doc/04_architecture/compiler/perf/persistent_package_module_index_compile_optimization.md` |
| Detail design | `doc/05_design/compiler/perf/persistent_package_module_index_compile_optimization.md` |
| Concrete acceptance list | `doc/03_plan/sys_test/item6_compile_optimization_acceptance_2026-10-03.md` |
| Existing broad executable specification | `test/03_system/compiler/package_index/persistent_smf_package_index_spec.spl` |

## Current evidence and gaps

1. The release baseline contains cold HIR/full-index publication owners. Historical
   statements that publication is absent must not be repeated as current facts.
   Presence does not prove admitted production execution or warm performance.
2. The broad executable specification invokes
   `scripts/check/check-persistent-smf-package-index.shs`, which is absent at the
   inspected revision. Its scenarios remain unverified; their expected receipt
   strings are not evidence. `/bin/sh` also requires an explicit host contract.
3. `package_index_route_current_v1` accepts one public-interface-change boolean
   for all changed modules. Per-module invalidation already exists below it.
   A mixed public/private batch needs production classification and adoption,
   not merely a new unused helper or a test-provided truth flag.
4. Publication uses a current-generation lock. GC must participate in the same
   transaction so it cannot delete a newly published generation after reading
   the old pointer. A deterministic held-lock test is the first repair target.
5. `bin/release` is absent in the inspected Windows workspace. Runner discovery
   must validate binary provenance and non-vacuous execution. Wrapper fallback
   to a Rust seed cannot qualify any row.

## Execution stages and acceptance evidence

| Stage | Work | Evidence required before completion |
|---|---|---|
| A | Reconcile source owners, existing requirements and primary-source research | Exact revision/path references and explicit evidence gaps |
| B | Bind immutable inventory, index generation, compiler/target/config identities | Mutation tests prove stale or mixed bindings reject before reuse |
| C | Serialize publication, pinning and GC; reject corruption | Deterministic race/crash tests preserve one complete readable generation |
| D | Classify changes per module using admitted prior/new semantic metadata | Mixed public/private edit compiles only producer and exact consumers; unchanged export cuts off propagation |
| E | Admit action/archive/local/remote reuse and generated inputs | Forgery, truncation, unknown input and cross-variant cases reject; fresh/hit artifacts and diagnostics agree |
| F | Adopt route in compile/check/bootstrap/daemon/MCP/LSP | Production boundary counters prove no hidden recursive scan or unrelated source reads |
| G | Measure clean/warm/no-op/edit stages and RSS | Pinned quiet-runner samples meet existing NFR budgets; missing or noisy samples are INCONCLUSIVE |
| H | Review, verify and land | Required runtime checks and exact-head review, release-target PR merge, shared-fix main port |

Stages are a dependency order, not permission to omit later stages. A focused
GC fix does not close mixed invalidation, CLI acceptance, or performance gates.

## TDD and modern SSpec contract

Use `describe`, `context`, `it`, explicit readable `step("...")` actions and
built-in matchers. Import actual production owners for narrow deterministic
regressions. System fixtures must drive the compiler and inspect its emitted
artifacts/counters; no test-side graph algorithm or canned success receipt.
Record the pre-fix failure, changed source, post-fix result, binary digest and
source revision. A missing runner is BLOCKED, not a RED behavior failure; a
missing checker is a harness failure, not proof the compiler is incorrect.
Generate manuals from the admitted executable spec, and keep `.spl` outside
`doc/06_spec`. Preserve precise requirement-to-scenario links.

Run each unchanged acceptance criterion once. At most three fix/verify cycles
per defect. Qualification checks cannot be replaced by source-string checks.
Required compiler/lib/MCP/LSP checks, runtime/native smoke, env facade audits,
and executable-spec layout checks remain explicit before landing as verified.

## Parallel ownership and integration

All lanes start at the exact release baseline above, in distinct linked
worktrees and `work/*` branches. Root owns this plan/design and integration;
`item6_research` owns additive local/domain research; `item6_acceptance` owns the
acceptance audit and specification planning; `item6_runtime` owns the GC race
regression and production fix. Lower-model sidecars: N/A. Root performs final
code and evidence review. Agents commit only their named files; root integrates
reviewed commits, never unrelated root-worktree changes.

Shared interfaces retain actual production names, including
`PackageIndexRouteV1`, `package_index_route_current_v1`,
`PackageModuleChangeV1`, and `package_module_index_gc_v1`. Planned record names
must not be presented as implemented APIs. New steps use concrete actions such
as `Admit the current package index`, `Reject a changed index binding`, and
`Preserve the prior admitted generation`. Unimplemented cases stay explicitly
blocked or fail; they never use placeholder passes.

Target `release/1.0` through a reviewed work-branch PR. Shared fixes also need
an isolated main-targeted forward port and renewed applicable evidence. No
release tag or publication is implied by this development request.

## 2026-10-09 release-lane revalidation

Continue from the retained stages above. See
`doc/09_report/item6_compile_optimization_release_revalidation_2026-10-09.md`
for current source ownership, the stage inventory, actual bounded gate results,
and continuation order at release revision
`df266ee64b5a6b8590b0f62b2624455d5e4a6236`.

The acceptance checker now exists and drives a compiled owner artifact; its
historical absence is not a current source finding. Admitted semantic-transition
routing and publication/GC locking also exist. Their presence does not supply
runtime acceptance. The snapshot-derived root-generation gap remains present,
the compiled acceptance artifact is unavailable in this isolated worktree, and
both inspected Windows binaries explicitly identify as Rust seeds. Item 6
remains **BLOCKED / IN PROGRESS**, with no performance or qualification PASS.

## 2026-10-11 requested release_phase3 continuation

The user's current landing target is `release_phase3`; the complete A-H scope
above is retained. See
`doc/09_report/item6_release_phase3_readiness_2026-10-11.md` for current ownership,
focused provenance repairs in draft PR 3098, the located migration draft PR
3072, and exact bounded evidence. Neither draft is admitted for landing.

Current source contains retained indexing, semantic routing and corruption
guards, but generated compilation still rejects missing independent producer
authority. PR 3072's witness migration does not implement selected producer
execution or derived immutable snapshot consumption. These are Stage E
implementation obligations. Production compiler/filesystem observations,
all 44 scenarios, Phase 3/full CLI/core/MCP/LSP and Stage G measurements remain
unverified. A new pure-Simple acceptance-entry diagnostic build timed out after
240 seconds with no executable; its stopped cycle and cache are preserved.
Do not retry either lane's stopped three-cycle bootstrap/build campaign.

## 2026-10-25 status reconciliation (verified against `origin/release/1.0.0`)

Verified by `git merge-base --is-ancestor` of each merge commit and by reading
the current default sites. Host claims are limited to code presence; **no
native Stage 3 run of the per-file pipeline on this source exists yet**, so no
compile-time, memory, or first-object number below is a retained measurement.

| Area | Status | Evidence (PR / merge sha) |
|---|---|---|
| Per-module lowering instead of whole-program MIR | DONE | #4525 `2382dd7869f`, scripts #4547 `35789f8bb55` |
| True per-file pipeline design (contract, gaps, packages) | DONE (doc) | #4564 `8914716a114` → `doc/05_design/compiler/incremental_build/true_per_file_pipeline_v1.md` |
| Object streaming during MIR | DONE (default batch 8) | #4566 `ae96dd0bb6e` |
| `--file-worker` claim loop, HIR→MIR→obj per module | PARTIAL — opt-in | #4576 `106ab239fff`, #4584 `ab8be8ced3b`, #4585 `0b4822e703c`, #4588 `e0efb59638f` |
| Module-scoped mono + COMDAT, per-file mono, relocation, dedup | PARTIAL — opt-in | #4575 `00e0ab21f0b`, #4580 `29250ecf501`, #4597 `7ec523277de`, #4598 `220b35b4b35`, #4603 `cbe361c2497` |
| Incremental planner + object cache in file-worker pool | PARTIAL — opt-in lane | #4594 `9314979e6e6`; planner #4511 `f37c76ddaf4` |
| Default flip readiness + overlap receipt check | PARTIAL — prepared, **not flipped** | #4592 `1c6ccfb61c4`; `NATIVE_PER_FILE_PIPELINE_DEFAULT_V1 = "0"` (`src/compiler/80.driver/driver_build/native_file_worker_v1.spl:45`) |
| TLDR specialization list + `.rr` producers (P-G2) | OPEN — PR #4600 not merged | — |
| HIR phase speed (admission O(n²), lazy validation blobs, cache scope publish) | DONE (code); speedups are PR-reported, not re-measured | #4557 `4ce52b4d99f`, #4562 `5e8ad7e3638`, #4565 `700a2f742a4`, #4567 `24889530ad3` |
| Packed `.spab` parse cache | DONE — default store (`SIMPLE_FRONTEND_SPAB=0` opts out) | #4436 `387470fb5b3`, #4445 `2400d260405`, #4582 `2e958d33746`, #4589 `d1ee8738d60` |
| Generic TLDR view / instance cache / reader instances | DONE (code) | #4389 `9de5aade86a`, #4403 `5c8390bd95c`, #4433 `eba045f665c`, #4591 `3383735e8cb` |
| Cache limits (bytes, entry counts, usage ledger) | DONE (code) | #4396 `92a9517a17e`, #4405 `a4e59c4fc37`, #4506 `1859d0f69a8` |
| Content-keyed Stage 2 cache lane | DONE | #4559 `b73459ca0e0` |
| ParseContext (item 32) — prerequisite for in-process fibers | PARTIAL — stage 2 of plan | #4502 `0410c704cda`, #4568 `cb75218efa6` |
| MIR correctness fixes on the per-module lane | DONE | #4498, #4528, #4536, #4537, #4543, #4545 |
| Retained baselines (clean/warm/no-op/single-edit), semantic-invalidation matrix, corrupt-cache recovery, bootstrap/MCP/LSP equivalence | OPEN | none recorded on this source |

Done gate (umbrella §6) is **not met**: the per-file pipeline is opt-in, its
first-object overlap has no native receipt, and no retained end-to-end
compile-time/memory target has been measured.
