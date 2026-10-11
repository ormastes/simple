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
