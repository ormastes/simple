<!-- codex-research -->

# Simple + Spipe Release, Branch/Tag, Test-Repair, and Bootstrap Scheduling Hardening Plan

**Status:** Proposed architecture and implementation plan
**Audit date:** 2026-08-26
**Simple snapshot last observed:** `78e803b12aa00ae59e0d40630c8b3ab2fa63f4f3`
**Spipe snapshot last observed:** `4527ac41dee1774820605dde10d0f209fa5eb608`
**Scope:** `ormastes/simple`, `ormastes/Spipe`, their generated LLM skills, VCS/release policy, GitHub configuration, release CI, compiler/bootstrap orchestration, build diagnostics, and focused test-repair loops.

> This is a static source/configuration audit and design plan. It does not claim that the repositories build or that their test suites pass at the snapshots above; no local build or test execution was performed for this report. Simple's `main` advanced while the audit was in progress, so the SHA above is the latest observed head and individual file evidence was fetched from `main` during the same audit window.

## Executive decision

Adopt a protected-trunk, isolated-session, promote-not-rebuild release model:

1. One LLM session owns one physical worktree/workspace, one unique branch/bookmark, and one private output namespace. The main worktree is read-only for authoring.
2. `.spipe/policy/vcs.sdn` is the sole VCS policy authority. Human rules, generated model skills, CLI/MCP behavior, GitHub rulesets, and local checks are generated from or checked against it.
3. `release/version.sdn` is the sole version authority. `VERSION`, source constants, manifests, release notes, and tag names are checked projections.
4. `main`, `release/*`, `candidate/*`, and `v*` tags are server protected. Ordinary sessions never update them directly.
5. Artifacts are built once from an immutable candidate revision, tested and attested, then promoted unchanged. Release tags are outputs of admission, not inputs to untrusted builds.
6. Release tags are signed, annotated, immutable, exact-push only, and never routinely moved or deleted.
7. Compiler diagnosis performs complete discovery, then focused rebuild/test repair until clean, followed by one clean whole-suite confirmation.
8. Bootstrap becomes a speculative DAG: after phase X produces a minimally admitted compiler, phase X+1 starts on the critical path while phase X qualification runs concurrently.
9. Descendants stay quarantined until all ancestors qualify. A late correctness or provenance failure recursively invalidates all descendants and forces regeneration.

Retain immutable bootstrap authority generations, snapshots, stage receipts, rejected artifact preservation, private cache lanes, progress evidence, whole-test support, and multi-platform lanes. The main redesign is the control plane and policy authority.

## Highest-priority findings

### P0-A — Written policy and server reality disagree

The typed VCS policy models protected integration and release refs, signed immutable tags, isolated workspaces, and denied direct mutations. The audited GitHub state reported `main` unprotected and no repository rulesets for either repository. Server rulesets and drift verification must therefore be release blockers; local hooks are insufficient, particularly for JJ paths.

**2026-08-26 implementation update:** the original observation above is
historical. The Simple repository now passes the generated live-policy verifier
with seven rulesets, the declared protected-integration/release/npm-release
environments, and immutable releases enabled. This closes the configuration
drift row only. It does not supply Stage 3/4, whole-suite, signed beta,
immutable-candidate publication, or npm publication receipts.

### P0-B — Human and LLM rules still require direct `main`

Current VCS instructions include “no branches; work directly on main,” and `scripts/check/land.shs` moves and pushes `main`. This conflicts with typed policy and concurrent-session isolation. Remove direct-main authoring; only an integration authority may update a protected target by compare-and-swap after exact-revision gates pass.

### P0-C — Release skills tag too early and describe destructive rollback

Current release paths manually update multiple version locations, commit in the active workspace, create unsigned annotated tags, move `main`, and describe deleting releases/tags as rollback. Split preparation, candidate admission, tag signing, artifact promotion, publication, withdrawal, and operational rollback. Published versions are burned.

### P0-D — Release CI permits degraded artifacts

Release workflows contain useful whole-suite and platform coverage, but also `continue-on-error`, `|| true`, seed/committed-binary fallbacks, and source-only packaging. Required jobs must fail closed. Optional/unsupported targets must be declared explicitly in a support manifest and never impersonate required binary artifacts.

### P0-E — Bootstrap evidence is strong but orchestration is sequential

The existing wrapper has substantial provenance and admission checks, but serializes most Stage 2–6 work. It references a missing optional `bootstrap-strategy.sh`. Add a scheduler above the stage engine and split stage production from broad qualification so the next phase can begin after minimal admission.

## Normative model

- **Work item:** one traceable feature, fix, refactor, release preparation, backport, or hotfix.
- **Session:** one human/LLM context with a unique ID, branch, workspace, owner, and output namespace.
- **Integration target:** protected `main` or `release/X.Y`.
- **Candidate:** immutable exact revision plus admitted artifact manifest, named `candidate/vX.Y.Z[-pre.N]/aNNN`.
- **Release:** a candidate promoted without rebuilding and bound to a signed `v...` tag.
- **Provisional compiler:** a phase compiler passing the minimal safe-execution gate.
- **Qualified compiler:** a compiler whose assigned validation passed.
- **Invalidation:** recursive revocation of an artifact and every descendant built from it.
- **Failure root:** failing test, compilation unit, target, or crashed diagnostic process.
- **Affected closure:** roots plus prerequisite, reverse-dependency, ABI, aspect, and generated-schema dependents required for sound rebuilding.

## Naming and ref policy

Protected refs:

| Ref | Purpose | Mutation rule |
|---|---|---|
| `main` | Integrated development | Integration authority only; no force/delete |
| `release/X.Y` | Stable maintenance | Integration authority only; never rebased |
| `candidate/vX.Y.Z[-pre.N]/aNNN` | Immutable candidate attempt | Create once; no update/delete during retention |
| `recovery/YYYYMMDD/incident-id` | Breakglass evidence | Incident authority; append-only |

Session branches use `work/<kind>/<work-id>-<slug>`, with kinds `feat`, `fix`, `refactor`, `perf`, `test`, `docs`, `build`, `chore`, `patch`, `hotfix`, `backport`, `release`, and `recovery`. Work IDs are `gh-N`, `sp-ID`, `local-YYYYMMDD-NNN`, or `incident-YYYYMMDD-NNN`; local IDs are allocated atomically by Spipe.

Future release tags are `vX.Y.Z`, `vX.Y.Z-rc.N`, `vX.Y.Z-beta.N`, or `vX.Y.Z-alpha.N`: signed, annotated, immutable, and individually pushed. Existing irregular tags remain frozen in `release/legacy-tags.sdn` and are excluded from new version selection.

## Session isolation

Every mutating skill starts through `spipe session start`, which resolves an exact target SHA, checks policy, allocates a session ID, creates a unique branch and linked worktree/JJ workspace, creates private logs/temp/output/cache-overlay directories, records an immutable manifest, and locks ownership. A JJ workspace without a unique exported bookmark/branch is insufficient.

The main worktree permits read-only inspection, fetch, session supervision, policy drift checks, and viewing published artifacts. It rejects edits, commits, tags, release preparation, bootstrap publication, and protected-ref mutation.

Caches use shared read-only content-addressed objects plus session-private writable overlays and atomic verified publication. Keys bind parent compiler, source closure, runtime/toolchain/policy digests, target, backend, build mode, optimization, feature/aspect configuration, and normalized environment. Never share one mutable `build/` directory across sessions.

Session cleanup requires a clean workspace, no unpushed owned commits, archived integration/rejection receipt, no live process lock, disposition of outputs, and no unresolved review/release ref. Dirty expired sessions are preserved. `.sdn` conflicts require semantic merge, regeneration, explicit resolution, or fail-closed behavior—never blanket ours/theirs.

## Feature isolation and integration

One branch contains one semantic change. Do not mix unrelated cleanup, broad renames, policy edits with hand-edited projections, release bumps with implementation, or compiler changes with document-tree rebalancing. Target 400 non-generated changed lines, warn over 800, and require splitting or architecture-approved override over 1,200. Generated changes are counted separately and require deterministic regeneration evidence.

Private unsubmitted `work/*` refs may rebase under owner lease. Submitted changes require renewed review after rebase. `main`, `release/*`, `candidate/*`, recovery refs, and release tags never rebase or force-update.

Because these are personal repositories, implement an Spipe/SJ serialized integration queue: read the remote target, materialize an isolated integration worktree, apply the submitted change, run admission on the exact merged revision, re-read the target, and update only by CAS if unchanged. Otherwise discard and retry against the new target. Default integration squashes one semantic branch while preserving work ID, JJ change ID, review/test receipts, and backport trailers.

Normal fixes target `main`. Patch work targets `release/X.Y`. Hotfixes start from the affected tag/line, remain minimal, land on the maintenance line, and forward-port to `main`. Backports record source commit/change identity, target line, and adaptation reason.

### Audit addendum — periodic bootstrap/release-line convergence

An active beta/bootstrap lane periodically fetches and compares exact `main` and
`release/X.Y` revisions, but discovery is read-only. It may propose reviewed bug
fixes; it may not automatically cherry-pick, merge, push, or choose fixes. A
selected shared fix crosses through an isolated work branch/worktree, renewed
review and focused evidence, a divergence receipt, and protected CAS integration.
Normally the fix lands on `main` and is backported. If an emergency fix lands on
the release line first, candidate qualification requires a reviewed forward-port
to `main`, unless review records that the change is release-line-only. `main`
always remains the independent development trunk: it never tracks, becomes, or
is reset to the release branch, and neither protected ref is pushed directly by
the bootstrap session.

## Version and release policy

`release/version.sdn` projects into `VERSION`, compiler/bootstrap identity, core/package manifests, release notes, and tag checks. Add `simple release version render|check|bump`. Check fails on stale/missing projections, unexpected product-version literals, case drift, package drift, or compatibility-dimension drift.

Compatibility dimensions include language/API, compiler ABI, bootstrap protocol, package format, SCV schema/wire, DevHub provider API, Spipe skill/plugin API, release manifest schema, and bootstrap receipt schema. The checker derives the minimum SemVer bump and rejects a smaller one.

Create `release/X.Y` by first RC. Only release blockers, security/compatibility fixes, approved backports, version/release metadata, and directly supporting tests/docs belong there.

## Release state machine and process

States are: planned → preparing → reviewed → integrated → candidate-created → building → qualifying → admitted → awaiting approval → tagged → draft-release → published-immutable → package-publication-complete → closed. Failure states include blocked, candidate/artifact rejected, approval rejected, partial publication, and withdrawn. Every transition consumes and emits typed receipts.

1. Preflight verifies repository/worktree identity, typed policy and generated projections, live ruleset fingerprint, actual ref protection, release environment, canonical version agreement, tag collision, and concurrent release-prep ownership.
2. An isolated release session freezes target SHA, source/subproject/policy/toolchain digests, and lockfiles.
3. Release preparation contains only canonical version/projections, notes, compatibility declaration, support tiers, migrations, and blocker references. It creates no tag.
4. Review and integrate through the CAS authority; build from the exact integrated commit, not the old branch head.
5. Create immutable `candidate/v.../aNNN`, whose manifest binds version, commit, target, source/policy/version/toolchain digests, required/optional platform profiles, graph schema, creator, and time.
6. Build required artifacts once into CAS. Prohibit seed/old-binary/source-only fallback, rebuild after approval, and tolerated required-job failures.
7. Qualify bootstrap lineage, whole tests, compiler regressions, critical tools/libs, packaging, CLI identity, compatibility, platform matrix, SBOM, checksums, provenance, vulnerability/license policy, and reproducibility/semantic equivalence.
8. Sign one admission record over candidate commit, all artifacts and evidence digests, version/support/policy manifests, and lineage root.
9. Require a protected release environment with reviewer, no self-review, constrained refs, least privilege, and signer/build identity separation.
10. Sign an annotated tag at the exact admitted commit and push exactly that ref. The message binds candidate, release/artifact manifests, lineage, and policy hashes.
11. Create a draft release, attach exact assets, verify digests and identity, publish immutably, and record release/attestation identity.
12. Publish package registries from exact admitted artifacts without rewriting versions or rebuilding. Retries are idempotent.

Rollback means redeploying a previous good release. Withdrawal keeps tags/assets/history and publishes an advisory. Source correction receives a new patch/prerelease. Tag deletion or movement is not routine rollback.

## GitHub enforcement

Rulesets for `main` require PR/integration authority, aggregate admission, resolved conversations, stale approval dismissal, signed integration commits, linear history, no force/delete/bypass, metadata/name policy, and drift checks. `release/*` adds scope/backport/compatibility checks and forbids rebase. `candidate/*` is authority-created and create-once. `v*` requires release authority, SemVer, signature, annotation, admission, and immutability.

Add CODEOWNERS for policy, release, workflows/rulesets, bootstrap, landing, build, compiler, Rust seed, and generated model skill sources. Default workflow permission is read-only; isolate write, OIDC, and attestation rights to their jobs; pin actions by full SHA; disable persistent credentials except controlled writes; never expose secrets to untrusted PR code; bind release jobs to protected refs and exact admitted candidates.

Generate expected server policy from `.spipe/policy/vcs.sdn` and expose `spipe vcs policy render-github|diff-live|verify-live`. Live verification blocks integration, candidate creation, tag creation, and publication.

## Complete discovery and focused repair

Use three modes:

1. **Complete discovery:** parse selected files through recoverable boundaries, continue semantic analysis with poison/error nodes where sound, isolate files/processes on crashes, build every target whose prerequisites passed, compile all possible test executables, and run every runnable test. Record every skipped, blocked, timed-out, OOM, or crashed unit.
2. **Focused repair:** after a change, compile failure roots and sound affected closure; rerun prior failures plus tests invalidated by changed interfaces. Preserve unrelated successes only within the same immutable input generation.
3. **Whole confirmation:** after focused failures reach zero, freeze a new snapshot and perform one clean whole required build/test confirmation. New failures reopen focused repair, followed by one more whole confirmation.

The repair build set includes failed and changed units, missing prerequisites, reverse dependencies for changed public interfaces, aspect/macro/weaving invalidation groups, and linker/package consumers of changed ABI. Private-body changes may reuse dependents only when interface hashes prove stability; unknown impact over-invalidates.

Add full diagnostic options equivalent to `--all-errors`, `--continue-files`, `--isolate-files-on-crash`, and `--emit-failure-manifest`. Infrastructure needs parser synchronization points, poison types, per-file transactions, stable diagnostic IDs/spans, incomplete-analysis markers, configurable limits, process resource limits, and final selected/complete/partial/crashed diagnostic counts.

The failure manifest binds run, source, compiler, policy, target/profile, discovery completeness, compile/test failure signatures, blocked units, interface impact, and infrastructure failures. Same input plus same failure signature twice triggers `BLOCKED_NO_PROGRESS`. Retries without changed inputs classify flakes/infrastructure; they are not repairs. A required flaky test blocks release unless explicitly quarantined with owner, issue, expiry, and platform scope.

Proposed commands include `simple check --discover-all`, `simple build --repair-from`, `simple test --rerun-from`, `simple test --whole-confirmation --fresh-results`, and `spipe repair status|next|close`.

## Bootstrap scheduler redesign

Preserve the existing phase model and trust primitives: Rust seed/runtime authority; minimal phase-2 compiler; self-hosting phase 3; full CLI phase 4; UI/MCP/LSP tools; whole release tests; snapshots, receipts, parent/child hash binding, sanity probes, admitted immutable copies, rejected preservation, verified-stage constraints, private caches, resource evidence, deployment receipts, and rollback copies.

Compiler states are Absent → Building → Built → SmokeAdmitted → Qualifying → Qualified → ReleaseAdmitted, with Rejected, Invalidated, Cancelled, and InfrastructureBlocked failure states. `SmokeAdmitted` verifies executable identity, stable hash, valid parent/source/runtime/tool receipts, a minimal compile/link/run fixture, no seed/stub/delegation violation, and publication to quarantined immutable storage.

At `SmokeAdmitted(C_X)`, immediately enqueue high-priority `BuildCompiler(C_X → C_X+1)` plus parallel compile-all, assigned Simple tests, critical library/tool builds/tests, compiler sanity, ABI/schema, backend parity, and resource regression checks for C_X. Minimal compilers may be driven by a trusted host orchestrator through their admitted compile interface.

Children of provisional parents may perform only quarantined speculation. They cannot deploy, update `bin/simple`, satisfy protected checks, publish candidates, sign releases, or populate trusted shared caches. Promotion requires a qualified ancestor chain.

Generation identity binds run epoch, phase, parent compiler/receipt, source revision/closure, runtime/tool authorities, policy, target, backend/mode/flags, and normalized environment. Every task has a generation lease and may publish only while current and untainted.

Correctness, miscompile, parser/semantic/codegen/runtime ABI, provenance, identity, authority drift, receipt mismatch, deterministic critical failures, and unknown failures invalidate the compiler and all descendants. Cancel running descendants, mark completed artifacts tainted, preserve rejected evidence, repair and mint a new epoch, then rebuild every descendant even when byte identity seems likely. Network/runner outages and resource exhaustion retry under bounded infrastructure policy unless artifact corruption is indicated.

Use CPU, memory, linker/LLVM, I/O test, emulator, and exclusive deploy/sign token pools. Reserve resources for the phase X+1 compiler critical path; qualification consumes the remainder. Default speculation depth is bounded by mode and memory.

Refactor the monolithic wrapper into idempotent `bootstrap step ...` commands plus `bootstrap graph run|resume|invalidate`. First add the missing compatibility supervisor, extract existing stages behind exact receipts, emit machine-readable events, then implement the scheduler in Simple while retaining a recovery shell boundary.

Release admission requires a wholly qualified, untainted lineage; exact hashes/receipts; whole Simple confirmation; critical tools/libs; required platforms; no fallback; stable snapshots; complete support/SBOM/checksum/provenance evidence; reproducibility; and an unchanged candidate ref.

## CI redesign

- `pr-admission.yml`: policy/projection drift, naming/scope, affected checks, path-sensitive bootstrap, evidence manifest, aggregate admission; support `merge_group` after organization/native queue migration.
- `candidate.yml`: freeze candidate, run bootstrap DAG and required matrix/whole/tool/lib/package checks, generate SBOM/provenance/checksums, and emit admission without needing a tag.
- `release-promote.yml`: protected manual invocation verifies policy and immutable candidate/assets, signs one tag, and publishes a draft release. It never builds.
- `publish.yml`: triggered only from immutable admitted release data and publishes exact artifacts.

Remove ambiguous success and fallback from required jobs. Define Tier 1, Tier 2, and experimental support in `release/support.sdn`. Candidate concurrency keys bind commit and policy; release keys bind version; artifact identities cannot be overwritten.

## Spipe changes

Create one semantic source for VCS/session, release, sync/rebase, worktree, integration, repair, and bootstrap-scheduler behavior, then generate/check Claude, Codex, Gemini, pipe, embedded Simple, CLI/MCP help, and human guides. Record source hash and semantic policy version in every projection.

Rewrite release into `/release start|prepare|candidate|status|promote|publish-status|withdraw`; require an isolated release session and canonical version source; never move `main`, build during promotion, create unsigned tags, push all tags, or delete published tags. Rewrite `/sync` to rebase/push only the owned session branch with lease and renewed gates.

Add CLI groups for `spipe session`, `vcs policy`, `integrate`, `release`, `failures`, and `bootstrap`. MCP read tools expose session/policy/candidate/release/graph/failure state. Guarded mutations require session ID, exact workspace, expected target SHA and policy hash, capability binding, main-worktree rejection, dry-run planning, and protected approval at irreversible release boundaries. Expose no arbitrary push/update-ref/tag-delete tool.

Upgrade the incompatible pre-1.0 plugin workflow to `0.2.0` and declare session, release, candidate, failure-manifest, and bootstrap-graph schema capabilities. Projection tests reject “NO BRANCHES,” raw `main` movement outside integration authority, `git push --tags`, unsigned release tagging, release-tag deletion, noncanonical version reads, tag-triggered unadmitted builds, blanket SDN conflict selection, schema/hash drift, and main-worktree mutations.

## Implementation sequence

0. Stop unsafe mutations: enable rulesets, block force/delete, remove destructive rollback guidance, require exact tag pushes, reject release commands from the main worktree, and record the live policy fingerprint.
1. Establish policy/version/session/candidate authorities and projection drift checks.
2. Implement isolated sessions, owned branches/worktrees, private overlays, recovery, and cleanup; replace direct landing with submission.
3. Implement the protected CAS integration queue and backport/hotfix checks.
4. Split immutable candidate builds from promote-only releases; add support tiers, SBOM, attestations, signed tags, immutable publication, and exact package publication.
5. Implement complete diagnostic discovery, failure manifests, affected-closure repair, no-progress/flake controls, and final whole confirmation.
6. Extract bootstrap stages and implement the speculative DAG, leases, recursive invalidation, quarantine, and resource scheduling.
7. Close reproducibility and supply-chain gaps with deterministic timestamps, pinned tools/actions, independent rebuild/equivalence checks, attestation verification, and recovery/key-rotation exercises.

Parallel ownership should separate policy/schema, session/worktree, integration/release CI, diagnostics, bootstrap scheduler, Spipe projection/plugin, and adversarial verification. Integrate shared schemas first; each lane uses its own isolated session branch/worktree.

## Acceptance and fault-injection summary

Required adversarial tests cover concurrent session uniqueness, main-worktree rejection, stale-target CAS failure, invalid rebase/force behavior, semantic SDN conflicts, unsigned/lightweight/moved/deleted tags, asset substitution, required-job soft failure, mutable-ref promotion, policy drift, multi-error whole-file discovery, isolated compiler crashes, independent target keep-going, focused closure behavior, no-progress/flaky tests, whole-confirmation reopening, phase X+1 overlap, late-parent recursive invalidation, stale lease publication, mid-run source/policy drift, cache poisoning, resource starvation, generation resume, and skill/plugin semantic parity.

Completion requires all of these invariants:

1. No mutation without an isolated session.
2. No session without both a unique branch and unique worktree/workspace.
3. No direct protected-ref mutation.
4. No release tag before exact candidate admission.
5. No release rebuild after admission.
6. No published version identity rewrite.
7. No final PASS before focused failures are zero and whole confirmation passes.
8. No descendant compiler promotion unless every ancestor remains qualified.

## Repository evidence

Simple evidence: [`main`](https://github.com/ormastes/simple/tree/78e803b12aa00ae59e0d40630c8b3ab2fa63f4f3), [VCS rule](https://github.com/ormastes/simple/blob/main/.claude/rules/vcs.md), [sync skill](https://github.com/ormastes/simple/blob/main/.claude/skills/sync.md), [release skill](https://github.com/ormastes/simple/blob/main/.claude/skills/release.md), [typed VCS policy](https://github.com/ormastes/simple/blob/main/.spipe/policy/vcs.sdn), [version authority](https://github.com/ormastes/simple/blob/main/release/version.sdn), [landing wrapper](https://github.com/ormastes/simple/blob/main/scripts/check/land.shs), [bootstrap wrapper](https://github.com/ormastes/simple/blob/main/scripts/bootstrap/bootstrap-from-scratch.sh), [bootstrap rule](https://github.com/ormastes/simple/blob/main/.claude/rules/bootstrap.md), [release workflow](https://github.com/ormastes/simple/blob/main/.github/workflows/release.yml), [publish workflow](https://github.com/ormastes/simple/blob/main/.github/workflows/publish.yml), and [multi-platform bootstrap](https://github.com/ormastes/simple/blob/main/.github/workflows/rust-bootstrap-multiplatform.yml).

Spipe evidence: [`main`](https://github.com/ormastes/Spipe/tree/4527ac41dee1774820605dde10d0f209fa5eb608), [worktree skill](https://github.com/ormastes/Spipe/blob/main/.claude/skills/lib/worktree.md), [VCS agent](https://github.com/ormastes/Spipe/blob/main/.claude/agents/vcs.md), [release command](https://github.com/ormastes/Spipe/blob/main/doc/00_llm_process/skill_command/command/release.md), [Codex projection](https://github.com/ormastes/Spipe/blob/main/doc/00_llm_process/skill_command/skills/codex/release/skill.md), [pipe projection](https://github.com/ormastes/Spipe/blob/main/doc/00_llm_process/skill_command/skills/pipe/release/skill.md), [dispatcher](https://github.com/ormastes/Spipe/blob/main/doc/00_llm_process/skill_command/skills/pipe/release/repo_and_pull_req/skill.md), [plugin manifest](https://github.com/ormastes/Spipe/blob/main/plugin/manifest.sdn), and [parity build](https://github.com/ormastes/Spipe/blob/main/scripts/build.sh).

## External references

1. [Git tags](https://git-scm.com/docs/git-tag.html)
2. [Git worktrees](https://git-scm.com/docs/git-worktree.html)
3. [GitHub rulesets](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-rulesets)
4. [GitHub merge queues](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/configuring-pull-request-merges/managing-a-merge-queue)
5. [GitHub immutable releases](https://docs.github.com/en/code-security/concepts/supply-chain-security/immutable-releases)
6. [GitHub artifact attestations](https://docs.github.com/en/actions/how-tos/secure-your-work/use-artifact-attestations/use-artifact-attestations)
7. [GitHub environments](https://docs.github.com/en/actions/reference/workflows-and-actions/deployments-and-environments)
8. [Semantic Versioning](https://semver.org/)
9. [Conventional Commits](https://www.conventionalcommits.org/)
10. [Bazel keep-going](https://bazel.build/docs/user-manual)
11. [Cargo test](https://doc.rust-lang.org/cargo/commands/cargo-test.html)
12. [Rust bootstrap](https://rustc-dev-guide.rust-lang.org/building/bootstrapping/how-bootstrap-does-it.html)
13. [Go source installation](https://go.dev/doc/install/source)
14. [Small changes](https://google.github.io/eng-practices/review/developer/small-cls.html)
15. [SOURCE_DATE_EPOCH](https://reproducible-builds.org/docs/source-date-epoch/)
16. [SLSA](https://slsa.dev/spec/)
