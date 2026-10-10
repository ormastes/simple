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
6. The release cold producer used the inventory-derived SCV tree ID as
   `root_generation`, forcing conservative invalidation after every source edit.
   A stable workspace-root identity is now wired as a candidate, with a focused
   no-stub native helper PASS. Full transition behavior, exact invalidation and
   paired time/RSS remain unverified. The warm driver also reads
   `SIMPLE_PACKAGE_INDEX_CHANGED_MODULES` without an in-tree event producer,
   so automatic edited-source invalidation still needs wiring; see
   `doc/09_report/compiler/item6_stable_workspace_root_generation_2026-10-10.md`.

7. The legacy module action key also bound SCV revision/tree and the full
   inventory, causing every unchanged module to miss after any source edit.
   A semantic v2 key and migration reader are prepared, with a focused native
   probe awaiting an admitted current-source compiler. Full cache hit and
   time/RSS proof remain open; see
   `doc/09_report/compiler/item6_semantic_action_reuse_2026-10-10.md`.

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

## 2026-10-10 current-source continuation

The production source-closure callback crash is repaired at the driver call site, and a rebuilt pure-Simple Stage 2 candidate passed naming sanity. The outer compiler-test gate stopped before tests for a missing explicit MC/DC waiver record. Three bounded native action-key probe attempts then failed on Cranelift imported globals, a reduced source inventory, and LLVM invalid IR; the semantic v2 key has no execution PASS. See [the continuation report](../../../09_report/compiler/item56_release_continuation_2026-10-10.md). Stages E–H and the selected time/RSS gates remain open.

### 2026-10-10 bounded native publication result

The repaired transition pointer now admits the first V1 generation in the no-stub LLVM/core-C CAS fixture. The same executable stops at its later second-generation action-digest validation (exit 11); the fixture does not publish/read/pin that generation. See `doc/08_tracking/bug/package_index_native_publication_blockers_2026-10-10.md`. Item 6 remains in progress; full entrypoint and paired time/RSS gates are unrun. The three-cycle cap prevents another retry in this session.

### 2026-10-10 warm inventory revert gap

Two warm Item 5 probe launches stopped at `snapshot-index-drift` after a tracked compiler source reverted to HEAD but the inventory retained its temporary bytes. A fresh compiler cache did not repair the persistent source cursor. Explicit cold init rebuilt authority and reached HIR; that run then failed on the separate Item 5 type-closure issue. See `doc/08_tracking/bug/scv_warm_inventory_misses_revert_to_head_2026-10-10.md`. Item 6 needs an event-authority regression and repair before warm correctness, full-entrypoint, or paired time/RSS acceptance can be claimed.

### 2026-10-10 second-generation and warm-revert isolation

The native CAS fixture exposed struct copy-then-mutate aliasing in its own negative control and in the production snapshot-path route. Both now construct independent entries. The repaired fixture publishes a second V2 generation, but readback exits 4 with no emitted reason; the pointed-to index bytes hash to CURRENT and contain one complete framed entry. The warm-revert recovery candidate retries cold inventory once on snapshot-index drift; its 135-module native probe passes HIR and monomorphization but stops at unrelated MIR lowering, so runtime correctness is unverified. See the two linked bug notes. Full entrypoint cutover, persistent semantic-index acceptance, and paired time/RSS gates remain open.

### 2026-10-11 CAS decode root

The second V2 generation's readback fails at entry field 11 because a one-character native substring displaying `3` converts to nil through `to_i64()`. The exact failure and bounded byte-parser repair are recorded in `doc/08_tracking/bug/package_index_native_publication_blockers_2026-10-10.md`. Publication/readback acceptance and full entrypoint performance remain open.

### 2026-10-11 native readback repair verified

A bounded byte decimal parser replaces native substring `to_i64()` in frame, list, and generation count decoding. The focused no-stub 50-module native CAS probe now passes second-generation publish/read/pin and stale-CAS rejection; malformed one-digit frame cases also pass. See the package-index native publication bug note for receipts. Item 6 remains in progress until warm SCV recovery, full entrypoint graph publication, and matched time/RSS qualification pass.
