# Report 2 — CI, local/GitHub hooks, tests, dependency policy, and releases

**Date:** 2026-09-25  
**Status:** Proposed policy and migration plan. New commands and status names are illustrative.  
**Companion:** Report 1 defines action identity and execution; Report 3 defines retries, audit gaps, and acceptance gates.

## 1. Repository and branch policy

### Monorepo boundary

Keep the compiler, interpreter/loader, runtime/sosix contracts, language specifications, foundational libraries, and first-party consumers that routinely require coordinated changes in the same history. This is a coupling criterion, not a target percentage of code. LLVM's historical monorepo rationale supports atomic cross-project changes; it does not imply building every directory on every commit. [W27]

Do not perform an immediate top-level directory rewrite. Simple already contains first-party implementations as well as example submodules; audit ownership and duplication before merging content. A platform sample in `examples/` is not automatically the canonical implementation of that platform.

| Component class | Recommended placement | Validation policy |
|---|---|---|
| Shared language/compiler/runtime/API implementation | Core monorepo | Affected compile/test closure. |
| Tightly coupled OS/IDE/browser/RTL integration layer | Core monorepo when coordinated edits are routine | Target-specific tests, not universal full builds. |
| Small syntax examples and compiler regression fixtures | Core monorepo | Cheap compile/run selection. |
| Independently useful applications and studies | Separate repositories; optional submodule or locked fetch | Pinned compatibility canaries. |
| Large third-party source/forks, such as QEMU | Separate source with exact lock and provenance | Toolchain/external target, selected only when needed. |
| Developer workflow tools such as Spipe | Independent versioned tool; optional checkout | Its digest is an input only to checks/actions that use it. |
| Generated caches, binaries, traces, huge datasets | Artifact/CAS storage | Digests and manifests in Git, not repetitive blobs. |

The current registry includes SimpleOS, RISC-V, baremetal, browser, IDE, QEMU, ML/example applications, Spipe, and a payment submodule under a library path. Treat those as classification candidates, not automatic migration instructions. The payment path in particular deserves a dependency-boundary audit before accepting it as a prerequisite of the language core. [R07]

### Branches are versions, not component containers

Use `main` for integration, short-lived `work/<owner>/<topic>` branches or equivalent JJ bookmarks, and `release/X.Y` for supported maintenance. Tags identify immutable releases. Keep existing protected candidate/integration/recovery refs where they serve an explicit promotion workflow; do not turn them into permanent compiler/OS/GPU feature branches.

Platform, SIMD, GPU, runtime, and memory-mode variation belongs in configuration and provider selection. A release branch carries a coherent older line of the repository, not an alternative directory layout. LLVM's release process uses release branches; that is independent of submodules. [W28]

Each concurrent human/agent session uses its own Git worktree or JJ workspace and its own writable build/output area. Do not assume separate Git worktrees imply separate hook configuration or immutable workspaces. Git worktrees share repository machinery while maintaining separate working trees. [W21]

Preserve move-only/import-only changes separately from semantic edits when practical. Before landing, refresh against the current target branch and avoid stale whole-worktree snapshots. Use named ownership of paths and a deliberate integration review; a green branch from yesterday is not evidence for today's merged tree.

### Submodule contract

Submodules are acceptable for independent examples. The superproject's gitlink SHA is the authority; an optional tracking branch is a developer update convenience, not the reproducible dependency version. Git distinguishes checking out the recorded commit from updating against a remote branch. [W20] [W29]

For each admitted submodule: record role, allowed repository identity, commit, optional recursive pins, required/optional status, license/provenance information, and selected canary tests in SDN. Preserve `.gitmodules` as Git's native configuration; do not create a second conflicting SHA authority in a lockfile. An SDN inventory may copy the gitlink value for validation and must reject disagreement. For non-submodule dependencies, the SDN lockfile is authoritative.

The update transaction is: publish the child commit first; verify the pinned revision can be fetched in a clean authorized environment; update the parent gitlink/manifest; run selected canaries; merge through ordinary review. Do not publish a parent that references a developer-only child commit. Never use `git submodule update --remote` in an admitted build. Do not recursively fetch optional examples on every PR.

An API-breaking change across two repositories cannot be made atomic merely by updating a submodule pointer. Use a compatibility bridge and staged rollout, or move the tightly coupled code into the monorepo. For canary testing against a candidate compiler, record a deliberate toolchain override to the candidate digest while leaving the canary's own source revision pinned.

Sparse checkout and partial fetch can reduce checkout cost, but sparse checkout alone is not a promise of reduced repository-history transfer. The build planner must still materialize the full selected input closure. [W22]

## 2. One policy engine, many adapters

Extend `config/check/must_check_gates.sdn` and the existing tier runner rather than inventing independent local-hook, PR, and distributed policies. The registry already distinguishes tiers and push-blocking behavior. Keep its existing obligations and migrate them explicitly, with a coverage inventory showing which tier now owns each check. [R10]

Proposed gate metadata:

```text
GateSpec:
  stable_id, policy_version, owner
  phase, applicability_predicate, mandatory
  target/test selectors, required_execution_class
  timeout, cacheability, expected evidence kind
  migration baseline + expiry when necessary
```

A gate predicate must return `APPLICABLE`, `NOT_APPLICABLE` with evidence, or `UNKNOWN`. Unknown does not mean skip. Missing tools, missing snapshots, unmapped source ownership, and absent test artifacts are errors/incomplete results, not not-applicable outcomes.

A gate receipt binds the repository, source tree, base/merge candidate, submodule closure, policy/runner version, compiler/toolchain digests, selected action/test set, actual completed set, result digests, validation environment, and issuer. Do not use a timestamp-only “last green” marker. A signature authenticates the issuer and message; it is not proof that the issuer honestly executed the claimed work.

### Verdict model

| Verdict | Meaning | Admission |
|---|---|---|
| `PASS` | Every applicable mandatory item has valid completed/reusable evidence. | Eligible for that exact gate/scope. |
| `FAIL` | Code, test, policy, or integrity failure. | Block. |
| `INCOMPLETE` | Deadline, unavailable worker/tool, missing evidence, uncertain graph, canceled work. | Block ready/admission; allow draft workflow. |
| `NOT_APPLICABLE` | Trusted policy proved the gate has no work for this change. | Count as a satisfied non-applicable requirement, not a test pass. |
| `FLAKY` / `ISOLATION_SENSITIVE` | Failed once, later succeeded under retry/isolation. | Preserve the defect; separate explicit quarantine policy. |

Retain existing exit-code conventions during migration and add structured SDN outcomes. Never infer successful tests solely from exit zero or a textual “PASS” line. Require test discovery/execution counts, expected case identities where available, and a valid result artifact. Existing zero-execution protections should remain. [R03]

## 3. Sub-minute pre-PR plan

**Objective:** warm ordinary-change preflight P95 below 60 seconds on a named reference machine/profile. This is not a cold checkout SLA, not a guarantee for arbitrary changes, and not permission to truncate tests. Track both command execution and end-to-end wall time, including queueing, materialization, compiler retrieval, and cache verification.

The preflight performs changed-source parsing/type checking, affected code generation where required, dependency-policy lint, and all affected mandatory fast unit/contract/layer/feature tests. It can use exact cached evidence for unchanged actions. Tests run after their required changed artifacts are available; independent branches of the action DAG can run concurrently.

An illustrative warm budget is 2 seconds planning, 4 seconds lint/graph validation, 18 seconds affected compilation, 25 seconds test critical path, and 3 seconds result aggregation, leaving 8 seconds slack. These are engineering allocations, **not benchmark results**. Broad compiler changes or cold toolchains can exceed them legitimately.

At the deadline, emit a clear remaining-work list and `INCOMPLETE`, then let the user-created CI job perform the extended lane. Do not convert unfinished work into a success and do not classify ordinary deadline overflow as a semantic test failure. A fully completed fast gate and a complete merge-admission gate are separately named results.

### Correct selection algorithm

1. Resolve the exact base and proposed source snapshot, including staged content for a commit check and committed content for PR/push checks.
2. Compare the old and new tracked graph/configuration, accounting for deleted/renamed files and gitlink updates.
3. Compile/type-check changed modules against their real owning target configuration. Reject ownerless production files or assign an explicit supported synthetic check target; do not silently ignore unreachable new code.
4. Update authoritative interface/ABI/semantic fingerprints and propagate only justified compile invalidation.
5. Independently compute behavior-dependent tests, fixture/configuration impact, contract boundaries, and feature/layer owners.
6. Resolve exact required configurations, materialize the action DAG, use qualified cache hits, and execute misses.
7. Explain both selected work and any avoided rebuilds. Unknown dependencies broaden the plan or keep admission incomplete.

Watchers and editor-triggered prewarming may make a later preflight cheap, but the final receipt must be rebound to the exact submitted snapshot. No background warm cache can substitute for snapshot verification.

## 4. Unit, contract, layer, feature, and system tests

| Test class | Purpose and selection | Typical lane |
|---|---|---|
| Unit | Local behavior of changed/affected modules and functions. | Fast preflight. |
| Contract | Boundary shape and semantics: API/ABI/effects, serialization, plugin/resource ABI. | Fast or extended preflight whenever the boundary is affected. |
| Layer | Coherence of parser, semantics, runtime, UI, storage, etc. | Affected layer gate. |
| Feature | User-visible behavior crossing layers; mapped to feature-owned components. | Affected feature fast tests, then extended scenarios. |
| Integration/system | Processes, toolchains, packaging, host services, OS images. | Merge/main/nightly or mandatory risk-triggered PR lane. |
| Canary application | Real external SDK/language consumer compatibility. | Selected risky changes, nightly, release. |
| Hardware/performance/stress | Environment-dependent or exploratory coverage. | Specialized lane; do not present a reused unit pass as this coverage. |

Layers and features are independent classification axes. A feature may cross several layers; a module may support several features. Use explicit target/test metadata plus compiler-resolved dependencies, not a requirement that each file directly import its own system test. Small pure infrastructure can be covered by unit and boundary contracts; not every source file needs a unique end-to-end test.

Historical coverage is useful for prioritization and auditing test mappings, not a generally sound reason to omit runtime-dependent tests: new inputs may execute a previously untouched branch. During migration, unresolved ownership expands to the nearest complete layer/feature suite. Legacy mapping debt needs an owner and expiry, while newly introduced unmapped production code is rejected.

Run shadow full suites to compare selection against broader coverage, mutate dependencies to prove invalidation, and inject deliberate test failures to prove the runner reports them. Keep test-selection confidence separate from raw passing-case counts.

### Configuration coverage

Every target lists supported configurations and required execution classes. Fast CI uses a small baseline plus changes' mandatory affected targets. Nightly expands coverage; release validates the documented supported set. Pairwise combinations can reduce supplementary exploration but must not replace named mandatory configurations or known three-way interactions.

Changes to a shared parser, code generator, allocator, scheduler, runtime ABI, toolchain, or policy usually need broader validation than a local UI body edit. A compiler implementation change must build and test the **candidate compiler**, not test programs using only the unchanged seed executable. Bind the candidate binary/provider digest into every relevant test action.

## 5. Dependency-rule lint

Run checks from resolver/target edges, not only textual imports. Enforce allowed layer directions, module visibility, declared package dependencies, legal feature entry points, forbidden core-to-example dependencies, plugin ABI boundaries, and permitted cycles/SCCs according to the language's rules. Do not arbitrarily forbid legal type-only cycles while missing runtime cycles.

Treat macros, AOP weaving, generated modules, linker inputs, scripts, fixtures, dynamic plugin registries, and environment-dependent resolution as first-class edges. A policy change is itself an input affecting all governed targets. Incremental lint updates changed edges and validates the impacted graph; periodic whole-graph checking detects index drift.

Add a second check for hermeticity: undeclared file reads/writes, network, global working-directory/environment changes, and outputs escaping their sandbox. A process sandbox protects the host, but it does not isolate one thread's inputs from another thread in the same group. Qualified multiplex providers must use per-action virtual filesystems/output APIs; unknown tools run in separate sandbox processes. [W07] [W30]

For inherited architectural violations, permit a narrow, reviewed baseline keyed to the actual offending edge. New violations fail; removed violations must disappear from the baseline. A baseline must never become a blanket “ignore this layer” rule.

## 6. Local hooks and submission workflow

Git hooks are local executable hooks and can be bypassed; they are feedback conveniences, not the ultimate enforcement boundary. Keep a documented installer and do not overwrite an unrelated user's existing hook without preserving it. [W19]

| Entry point | Work performed | Suggested warm objective |
|---|---|---:|
| `pre-commit` | Staged-snapshot formatting, syntax/SDN validity, cheap secret/structure checks. | 1–5 s |
| Explicit `simple preflight` (proposed) | Changed/affected semantic compile and selected fast tests. | P95 <60 s |
| `pre-push` | Exact outgoing refs, cheap committed-tree integrity, receipt freshness/status. | <10 s |
| `simple submit` / existing landing wrapper | Require complete preflight before ready submission; otherwise draft with explicit pending work. | Mostly receipt reuse |
| Remote admission | Independently verify required evidence and exact merge candidate. | Correctness gate, not a hard 60 s cap |

For a new work branch, an incomplete preflight can still be pushed for draft CI or collaboration. It cannot become an admitted merge. This avoids trapping a developer on a host lacking the right native toolchain while preserving the user's pre-PR check requirement for ready submissions.

Pre-commit checks the staged tree, not a dirty worktree that contains unstaged fixes. Pre-push parses **all** ref updates provided on stdin, including new branches and deletions, and materializes the relevant committed trees. A new ref has no ordinary old SHA; choose the configured integration base. A deleted ref is a repository-policy event, not a compile request.

The existing dispatcher already preserves local hooks, clears Git plumbing variables before nested checks, and contains recursion defenses. Extend that path instead of creating a second installer that reintroduces the same recursion problem. Preserve Windows PowerShell and shell installation paths; use sosix/portable timeout handling rather than assuming GNU utilities everywhere. [R08]

The existing landing wrapper explicitly handles a Git-versus-JJ hook seam and gates committed content before submitting an owned `work/*` branch. Reuse that seam for the unified gate invocation. Test actual supported Git, JJ, and `sj` clients; never assume an alternate client invokes Git hooks. [R09]

`gh` is a CLI adapter, not a server enforcement mechanism. An approved `simple submit` path may invoke `gh pr create` or ready an existing draft after verification; direct use of `gh`, the web UI, or an API is still protected by remote required checks. No shell-string interpolation of branch names or user-controlled paths.

## 7. GitHub architecture and native merge-queue caveat

The read-only audit found a public, user-owned repository. GitHub currently documents native merge queues for organization-owned public repositories, or qualifying organization private repositories. Therefore this plan does **not** depend on native merge queues being available to `ormastes/simple`. [R01] [W23]

### Default integration path for the current repository

Keep PR-required, up-to-date protection. Serialize integration using the existing protected candidate/integration workflow where practical: select the current base and PR head; build the exact candidate; collect required evidence; merge through the normal protected API path. If either base or head changes, discard the admission decision and revalidate. The integration actor must not use an always-bypass permission to sidestep these conditions.

The current main ruleset covers `main` and `integration/main`, requires PRs and strict required checks, and names `Code Idiom & Structural Ratchet Gates` and `SPipe Self Review Admission`. It also contains an always-bypass repository-role entry. Preserve the existing checks; add the new complete admission check only after qualification. Review bypass permissions explicitly rather than assuming “required” means unbypassable. This report does not change those settings. [R12]

If the repository later becomes eligible for native merge queues, add `merge_group: checks_requested`, run checks against the merge-group SHA, and preserve cancellation/receipt invalidation on group reconstruction. GitHub treats this as a distinct trigger. [W24]

### Trigger and result policy

| Trigger | Work |
|---|---|
| `pull_request` | Unprivileged candidate build/test on disposable workers; no trusted cache writes. |
| Existing base-controlled receipt verification | Verify trusted-policy receipts only; do not compile or execute head content in the privileged control context. |
| `merge_group` when eligible | Exact merge-group validation, not reuse of unrelated head-only admission. |
| Push to `main` / maintained release branch | Trusted integrated build, expanded tests, eligible cache promotion. |
| Scheduled | Full/shadow tests, bootstrap, platform matrix, cache soundness and performance audits. |
| Explicit release workflow | Candidate build/qualification and separately authorized publication. |

Avoid whole-workflow path filtering for required checks. Always schedule an aggregator that checks every applicable gate. Its success requires complete evidence; a skipped child job is not equivalent to a passed test. A documentation-only change can be legitimately non-applicable for compilation but still requires its document/policy checks. No `.spl` change is not the same as no relevant change: runtime C/Rust, SDN, CI code, generated inputs, or gitlinks may matter.

### Trusted control versus untrusted execution

The existing fast-PR workflow uses `pull_request_target` to verify signed local receipts from base-owned code and intentionally skips fork PRs. Replace the skip hole with a supported unprivileged validation path before making the check required. Its comments and code confirm it verifies receipts rather than compiling in that job. [R04]

Do not execute PR code on a privileged `pull_request_target` runner, expose release keys to compiler groups, or accept an arbitrary artifact from a PR as trusted evidence. Separate the trusted policy/check publisher from untrusted runners. An external GitHub App/check service or the existing protected-base verifier can publish admission only after validating scoped issuer credentials, job/action identities, and evidence. The head branch must not be able to rewrite the trusted policy and sign its own acceptance.

Pin third-party Actions to reviewed full SHAs, minimize token permissions, avoid persisted checkout credentials, and isolate fork work from persistent trusted worker caches and personal hosts. GitHub specifically warns about public PRs compromising self-hosted runners. [W25]

During policy migration, keep old and new gate names operating until rulesets are deliberately switched. Workflow renames, missing checks, or “success” from an untrusted producer must not silently satisfy the old requirement.

## 8. Build once, distribute tests, and control CI cost

Compile each unique action once per exact key, publish its validated result, and let independent test jobs consume the same artifact. Per-OS outputs remain separate when their action keys differ. Cache lookup comes before worker provisioning wherever possible. Use content-addressed toolchain retrieval so a fresh runner does not bootstrap the language from source just to run a fast check.

Introduce qualified precompiled seeds for each supported execution host. Record compiler, source/provenance, runtime, and payload digests. Missing seeds make the fast lane incomplete or route to the bootstrap lane; they never downgrade mandatory semantic checking to syntax-only. Keep seed build/update review separate from ordinary PR execution.

Avoid re-running expensive guard selftests on every unchanged local push. Qualify a guard against adversarial fixtures when its implementation/policy dependencies change; execute the actual selected guard on the current tree. Bound long full-tree scans by incremental graph data and exact cached evidence, never by deleting the obligation. The existing gate registry contains timing and advisory migration notes that make a deliberate tier map preferable to accumulating more push hooks. [R10]

## 9. Release and bootstrap policy

Define explicit bootstrap modes: use a qualified seed, rebuild the candidate compiler, self-host subsequent stages, test convergence, and perform a clean release qualification. The full clean lane excludes prior object/module/action-cache hits for the build under test, although immutable toolchain downloads can be reused. A stage-two/stage-three equality check establishes a particular convergence property, not universal compiler correctness or protection against every malicious seed.

Ordinary application PRs use the seed plus affected compilation. Compiler PRs build the changed compiler and exercise it. Runtime/ABI/bootstrap-critical changes escalate to the required stage chain before admission. Periodic and release validation runs the supported clean bootstrap and regression matrix.

Prepare version stamping and other byte-changing packaging inputs **before** the release candidate build. Validate compiler, SDK, runtime, packages, OS images, and their supported configurations by digest. Promote those exact unsigned artifacts; signing/notarization is an explicit subsequent action and its final package must pass installation/loading/integrity smoke tests. Do not rebuild silently after qualification and assume the new artifact is equivalent.

A release record binds source tree, dependency/submodule/toolchain locks, stage manifests, test evidence, package digests, signing provenance, and support matrix. A failed release leaves the previous qualified release and seed available. Repair a release line through a reviewed branch/PR; do not rewrite an already published tag to different bytes.

## 10. Rollout rules

Start by fixing the current semantic/check and action-identity blockers. Run the new selector in shadow mode beside the conservative selector. Then enable exact local cache reuse, provider groups, controlled remote execution, and only finally the new required admission check.

Repository migration, scheduler rollout, and CI-required-check activation are separate changes. A submodule import must not be bundled with an unqualified new cache mode and a ruleset replacement. Each rollout must have a fallback: conservative dependency closure, isolated processes, local execution, old checked gate policy, and an already qualified compiler seed.

## References

[R01]: https://api.github.com/repos/ormastes/simple "Simple repository metadata (read-only audit, 2026-09-25)"
[R03]: https://github.com/ormastes/simple/blob/ed75897fe050d874ce7c7bcd90c2b30953ad65ce/scripts/check/check-pr-fast.shs "Simple fast-PR checker; inspected lines 1–125"
[R04]: https://github.com/ormastes/simple/blob/ed75897fe050d874ce7c7bcd90c2b30953ad65ce/.github/workflows/pr-fast-check.yml "Simple fast-PR GitHub workflow"
[R07]: https://github.com/ormastes/simple/blob/ed75897fe050d874ce7c7bcd90c2b30953ad65ce/.gitmodules "Simple submodule registry"
[R08]: https://github.com/ormastes/simple/blob/ed75897fe050d874ce7c7bcd90c2b30953ad65ce/scripts/hooks/pre-push "Simple pre-push dispatcher"
[R09]: https://github.com/ormastes/simple/blob/ed75897fe050d874ce7c7bcd90c2b30953ad65ce/scripts/check/land.shs "Simple landing wrapper; inspected lines 1–95"
[R10]: https://github.com/ormastes/simple/blob/ed75897fe050d874ce7c7bcd90c2b30953ad65ce/config/check/must_check_gates.sdn "Simple canonical must-check registry; opening portion inspected"
[R12]: https://api.github.com/repos/ormastes/simple/rulesets/21573643 "Active main/integration-main ruleset, read on 2026-09-25"
[W07]: https://bazel.build/remote/multiplex "Bazel multiplex workers (documented as experimental)"
[W19]: https://git-scm.com/docs/githooks "Git hooks"
[W20]: https://git-scm.com/docs/gitsubmodules "Git submodules and independent histories"
[W21]: https://git-scm.com/docs/git-worktree "Git worktrees"
[W22]: https://git-scm.com/docs/git-sparse-checkout "Git sparse checkout"
[W23]: https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/configuring-pull-request-merges/managing-a-merge-queue "GitHub merge-queue eligibility and CI integration"
[W24]: https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows "GitHub workflow events"
[W25]: https://docs.github.com/en/actions/reference/security/secure-use "GitHub secure-use reference"
[W27]: https://llvm.org/docs/Proposals/GitHubMove.html "LLVM monorepo migration rationale (historical proposal)"
[W28]: https://llvm.org/docs/HowToReleaseLLVM.html "LLVM release process"
[W29]: https://git-scm.com/docs/git-submodule "Git submodule update behavior"
[W30]: https://bazel.build/remote/sandbox "Bazel remote-execution sandbox troubleshooting"
