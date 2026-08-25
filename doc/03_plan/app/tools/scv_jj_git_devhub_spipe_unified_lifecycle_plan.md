<!-- codex-design -->
# Unified lifecycle implementation plan

**Status:** Staged plan; no implementation started  
**Design:** `doc/05_design/app/tools/scv_jj_git_devhub_spipe_unified_lifecycle.md`

## Delivery rule

Each stage is a separate logical change, defaults to observe/dry-run mode, and
must preserve Git/JJ recovery authority until its exit gate passes. Shared IDs,
enums, provider capabilities, command registry, policy schemas, and fixtures
have one merge owner.

## Stage 0 — protected-ref safety

1. Document protected `main`, `integration/main`, `release/*`, candidate, tag,
   recovery, and review-ref classes.
2. Add `.spipe/policy/vcs.sdn` and an observe-only parser.
3. Make the gate manifest directly invocable against pinned BASE/HEAD.
4. Add a conformance matrix for every protected update spelling.
5. Route `land.shs --dry-run` through a typed planner and compare old/new plans.

Exit: no protected path reports success without complete gate evidence; raw
updates are detected and cannot create integration or release evidence.

## Stage 1 — lifecycle identity shadowing

1. Add ChangeId, RevisionId, alias records, encoding, migrations, and fsck.
2. Import JJ/Git identities without changing content authority.
3. Export an `SCV-Change-Id` trailer as an interoperability aid.
4. Add doctor checks for alias and tree equivalence.

Exit: every new JJ change has a stable SCV ChangeId and every snapshot maps to
verified exact SCV/JJ/Git identities across amend/rebase/export/import.

## Stage 2 — local review and integration

1. Add ReviewSession, ReviewRun, Finding, Approval, GateRun, and GateBundle.
2. Bind approvals to RevisionId and invalidate on change.
3. Add parser-aware anchor/reanchor and SARIF import/export.
4. Add bounded mock reviewer routes before connecting real model providers.
5. Add typed `IntegrateRequest`, dry-run planning, lease, CAS, and audit.
6. Enable mutation for `integration/main` only after parity tests.

Exit: a local-only change can be reviewed, escalated, approved, gated, and
race-safely integrated; concurrent candidates yield one CAS winner and one
clean retry.

## Stage 3 — canonical version and release lifecycle

1. Inventory version consumers once and declare them in `release/version.sdn`.
2. Add render/check/explain and drift-only CI.
3. Add ReleaseLine, ReleaseCandidate, Release, artifact, and provenance links.
4. Add candidate abandon versus published withdraw state transitions.
5. Add signed annotated tag dry-run and Git object verification.
6. Migrate one consumer, then the release skill after parity.

Exit: a candidate can be prepared and verified without hard-coded edits;
version/source/artifact/provenance identity is queryable and published tags are
immutability-enforced.

## Stage 4 — DevHub provider projection

1. Add provider capability traits, registry, RemoteBinding, SyncConflict, and
   durable outbox.
2. Add versioned JSON/idempotency/dry-run/explain contracts.
3. Implement typed GitHub review projection behind an experimental flag.
4. Round-trip review findings, threads, approvals, exact head, and release
   metadata without semantic flattening.

Exit: one local review projects to GitHub and returns without duplicate
findings; stale provider heads are blocked.

## Stage 5 — features, tasks, and wiki

1. Add Feature/Task/Document objects and relations.
2. Add feature manifests and generated virtual feature views.
3. Add field-authoritative three-way Jira/GitHub task sync.
4. Add Confluence/Git-wiki managed-region sync.
5. Keep `.spipe/run` process state separate and promote only checkpoints.

Exit: one feature links its documents, tasks, changes, reviews, and releases;
offline/remote concurrent edits produce explicit conflicts with no silent loss.

## Stage 6 — provider expansion and policy compilation

1. Add GitLab, Gerrit, Review Board, then complete Bitbucket via the common
   provider contract suite.
2. Add review/release/version/task/provider/model/authority policies.
3. Generate and verify Spipe skills, agent rules, guide tables, and gates.
4. Keep compatibility aliases until structured-command parity passes.

Exit: unsupported semantics fail explicitly, provider logic does not leak into
Spipe, and policy drift fails CI.

## Stage 7 — SCV content-authority promotion

Follow existing SCV S0-S6 migration gates: dual-write equivalence, backup and
restore, fault injection, recovery, conservative GC, and rollback proof.

Exit: only measured conformance promotes SCV from lifecycle authority to
content writer; Git/JJ rollback remains available until final approval.

## Ownership lanes

| Lane | Scope | Deliverable |
|---|---|---|
| Schema/integration | shared IDs, enums, capabilities, policy versions, fixtures | stable shared contracts and merge ownership |
| SCV lifecycle | `src/lib/scv/lifecycle/**` | identity, review, gate, release, work, binding stores |
| SJ gateway | `src/app/sj/**`, landing wrapper | typed operations, leases, CAS, gates, audit |
| Review | review library and DevHub review domain | state machine, anchors, SARIF, escalation |
| DevHub providers | provider registry/adapters and sync commands | capabilities, GitHub, binding/outbox |
| Version/release | `release/**`, DevHub release/version | manifest, projections, provenance, publication |
| Feature/task/wiki | DevHub work/document domains and adapters | manifests, virtual views, three-way sync |
| Spipe policy | policy, skills, guides, generated rules | thin clients and conformance |
| Verification | lifecycle/provider/fault-injection suites | adversarial bypass and recovery evidence |

Sidecar lanes: N/A for the initial shared-schema change. Later disjoint provider
and fixture work may use sidecars only after the merge owner fixes interface,
command, scenario-step, checker-helper, and fail-fast placeholder names. Merge
owner and final reviewer: best available normal/highest-capability maintainer.

## System-test plan

- Identity: rewrite/rebase/Git round-trip and alias recovery.
- Review: exact-revision invalidation, local-only flow, bounded escalation,
  implementer self-approval denial, SARIF and reanchor behavior.
- Integration: complete gate enumeration, missing-hook safety, concurrent CAS,
  remote-head change, network interruption, and break-glass audit.
- Provider: discovery, pagination, idempotency, ETag conflict, auth/rate limit,
  duplicate/out-of-order webhook, tombstone, and semantic-gap behavior.
- Release: projection drift, SemVer recommendation, candidate abandon,
  immutable publication, digest/provenance mismatch, back/forward-port duty,
  withdrawal and replacement.
- Fault injection: fail after each persistent boundary and prove idempotent,
  explainable recovery.

Executable SPipe specs should be introduced with their implementation stages,
not as passing placeholders. Every unresolved oracle remains fail-fast.

## Verification gates

For each stage, run its acceptance evidence once. Stop when green; allow at
most three fix/verify cycles. Before release, require zero executable specs
under `doc/06_spec`, direct environment/runtime audits, all affected compiler,
library, MCP/LSP checks, structured performance evidence for hot tooling paths,
and a full `$verify` `STATUS: PASS`.

## Immediate next change

Implement Stage 0 as five small dependent changes, beginning with the protected
ref classes and observe-only `vcs.sdn`. Do not enable a new mutation path in the
same change that introduces its policy parser.

## 2026-08-25 agent-base implementation handoff

The observe-only base now implements lifecycle value objects and canonical
record envelopes, stable change/immutable revision derivation, exact review and
gate admission, three-way sync conflict planning, immutable release
transitions, typed SJ operation/integration planning, VCS policy validation,
canonical version-manifest validation, and DevHub `devhub/v1` inspection.

Focused unit/system evidence is diagnostically green, but final verification is
open: the deployed `bin/simple` is the Rust bootstrap seed, so its test/docgen
results are not production evidence and it cannot execute `sspec-maintain` or
`duplicate-check`. Resume with the exact commands recorded in
`.spipe/scv_jj_git_devhub_spipe_unified_lifecycle/state.md` after an admitted
Stage 4 deployment. Unrelated working-tree guard failures remain with their
owning lanes and must not be folded into this implementation.
