<!-- codex-design -->
# Unified lifecycle architecture

**Research (authority):**
`doc/01_research/app/tools/scv/scv_jj_git_devhub_spipe_unified_lifecycle_full_2026-08-25.md`
(doc 1) and
`doc/01_research/app/tools/scv/scv_jj_git_unified_release_review_work_item_2026-08-25.md`
(doc 2). This document states decisions and seams; shapes live in
`doc/05_design/app/tools/scv_jj_git_devhub_spipe_unified_lifecycle.md`.

The architecture is a layered virtual capsule, not a new VCS or forge:

```text
Spipe orchestration -> DevHub lifecycle API -> SCV lifecycle graph
                                      \----> SJ typed transactions -> JJ/Git
                                      \----> capability providers
```

Public-to-next-layer rules:

1. Spipe can call only versioned DevHub/SJ operations and records returned IDs.
2. DevHub domain code can depend on SCV lifecycle values and provider traits,
   never concrete provider authentication or command text.
3. SCV lifecycle values cannot depend on JJ, Git, provider, CLI, or Spipe code.
4. SJ policy/planning can consume lifecycle evidence but cannot own review,
   work-management, or wiki semantics.
5. JJ and Git are backend aliases/transports; they never become canonical
   lifecycle identity.

<!-- sdn-diagram:id=scv_jj_git_devhub_spipe_unified_lifecycle.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_jj_git_devhub_spipe_unified_lifecycle.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

Spipe -> DevHub
DevHub -> SCVLifecycle
DevHub -> SJ
DevHub -> ProviderRegistry
ProviderRegistry -> GitHub
ProviderRegistry -> GitLab
ProviderRegistry -> Gerrit
ProviderRegistry -> ReviewBoard
ProviderRegistry -> Bitbucket
ProviderRegistry -> Outbox
Outbox ~> SCVLifecycle
SJ -> JJ
SJ -> Git
SJ -> GateEngine
GateEngine -> SCVLifecycle
Git -> CI
CI ~> SCVLifecycle
Spipe -x JJ
Spipe -x Git
ProviderRegistry -x SJ
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_jj_git_devhub_spipe_unified_lifecycle.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

Forbidden edges (`-x`) are architectural: Spipe never drives JJ/Git directly,
and a provider adapter never mutates a ref. Only SJ touches `.jj`/`.git`.

## Capsule placement (measured 2026-09-05)

The base capsule is `src/lib/scv/lifecycle/` (11 files, 896 lines): identity
derivation (`identity.spl:10-25`), digest-bound record persistence
(`store.spl:15-38`, `.scv/lifecycle/<kind>/<id>.scvl`), exact-revision review
admission (`review.spl:24-62`), escalation routing (`routing.spl:25`),
three-way field sync and the CloudEvents outbox (`sync.spl:30-72`), work-graph
validation (`work.spl:7-19`), release transitions (`release.spl:6-27`) and
operation audit (`audit.spl:18`). `src/app/sj/{operation,integrate_plan,
lifecycle_policy,gate_manifest}.spl` owns the typed mutation vocabulary and
pure planning. `src/app/devhub/cmd_lifecycle.spl` is the versioned inspection
surface (`lifecycle_capabilities_json`, `:59-60`, reports
`mutation: disabled-by-default`). `src/app/devhub/provider/lifecycle_provider.spl:9-31`
declares the five provider traits; **no implementer exists yet**.

MDSOC feature transforms are limited to audit/provenance emission at durable
operation boundaries. They must not hide ref mutation or provider writes.
Runtime composition belongs in provider adapters and SJ backends.

## Authority hierarchy

When SCV, JJ, Git, a provider, and a generated document disagree, resolve in
this fixed order (doc 1 §4.1); a lower level never overrides a higher one:

1. immutable source bytes/tree (SCV object hash + verified Git tree);
2. logical lifecycle identity (`ChangeId`, `RevisionId`, `ReviewId`, `FeatureId`,
   `ReleaseId`);
3. protected-ref state (SJ transaction record + remote CAS result);
4. gate/review evidence bundle;
5. remote provider metadata (`RemoteBinding`);
6. human-oriented projections, which can always be regenerated.

Canonical-vs-projected ownership follows doc 1 §4.2 verbatim; the one
policy-selectable row is task status (field authority per binding, Stage 5).

## Stage architecture

Stage numbering follows
`doc/03_plan/app/tools/scv_jj_git_devhub_spipe_unified_lifecycle_plan.md`.

### Stage 0 — protected-ref safety

Ref classes are **policy rows**, not code. The normative table (doc 1 §7.1)
maps one-to-one onto `ProtectedRefPolicy` (`src/app/sj/lifecycle_policy.spl:6-12`:
`ref_pattern / mutator / update / force / gate_profile /
server_enforcement_required`) and is carried by `.spipe/policy/vcs.sdn`
(schema `spipe-vcs/3`):

| Ref class | Pattern | Update rule | Force | Row in `vcs.sdn` |
|---|---|---|---|---|
| Public trunk | `main` | fast-forward or merge queue | deny | `:5` |
| Local reviewed trunk | `integration/main` | compare-and-swap | deny | `:13` |
| Release line | `release/*` | fast-forward | deny | `:20` |
| Immutable release tag | `refs/tags/v*` | immutable annotated signed | deny | `:27` |
| Ephemeral review projection | `review/*` | compare-and-swap (lease) | deny | `:34` |
| Staging candidate | `candidate/*` | create-once | deny | `:41` |
| Recovery refs | `recovery/*` | append-only | deny | `:48` |
| Private/security change | SCV private namespace | no public projection | n/a | **absent** |

`vcs.sdn` is stricter than doc 1 §7.1's force column (`review/*` and
`candidate/*` are `deny`, not "lease/CAS allowed"); the policy file governs.
The private/security row is a Stage 0 policy delta; ref lifetime/TTL (doc 1
§7.1 "Lifetime" column) is deliberately not a policy field — TTL enforcement is
a Stage 4 projection concern, not a ref-safety one.

The **planner** is `plan_integration*` (`src/app/sj/integrate_plan.spl:32-79`)
resolved through `lifecycle_policy_ref` (`lifecycle_policy.spl:311`). It is
fail-closed in this order: observe-only (`:33-34`, `SJ_OBSERVE_ONLY`), target
not a declared protected ref (`SJ_POLICY_TARGET`), missing identity, remote CAS
precondition changed (`:40`, `SJ_REMOTE_STALE`), missing policy/authority,
incomplete exact-revision gate bundle, no exact-revision approval. Server-side
rulesets (`vcs.sdn:107-117`) repeat the checks; hooks are compatibility only
(doc 1 §15.3).

### Stage 1 — lifecycle identity shadowing

`ChangeId` is stable across rewrites; `RevisionId` is derived from tree,
parents and policy metadata (`identity.spl:14`). JJ change/commit IDs, Git OIDs
and provider patchsets are verified aliases (`RevisionAliases`,
`model.spl:4`), validated by `lifecycle_aliases_validate` (`identity.spl:37`).
Nothing in Stage 1 mutates a ref.

### Stage 2 — local review and integration

Three cooperating mechanisms, all pure planning today:

- **Routing** — `ReviewRoutePolicy`/`review_escalation_admit`
  (`routing.spl:7-40`): depth, children-per-run, normalized-question cycle
  detection, human terminal for high/critical. Approval never comes from
  self-confidence alone (doc 1 §10.4-10.5).
- **Admission** — `lifecycle_gate_bundle_admits` (`review.spl:57`) and
  `lifecycle_revalidate_approval` (`review.spl:24`) bind approval to the exact
  `RevisionId` + policy digest + evidence digest; a rewrite invalidates it.
- **Lease + CAS** — the admitted plan is the nine ordered steps emitted at
  `integrate_plan.spl:54-64` (lease, fetch/CAS-compare, refresh+revalidate,
  pinned gate manifest, SCV/JJ/Git tree equivalence, CAS `integration/main`,
  export/publish exact ref, verify remote, durable audit). Gate invocations
  come from `plan_protected_gate_manifest` (`gate_manifest.spl:76`) over
  `config/check/must_check_gates.sdn` push-tier rows (the parser recognises
  that table header at `gate_manifest.spl:58`), so the transaction does not
  depend on `.git/hooks`.

Execution of those steps is the Stage 2 src-lane delta; the planner is
measured, the executor is not present.

### Stage 3 — canonical version and release lifecycle

Decision: one manifest, generated projections, evidence-driven bump, SJ-owned
tag, DevHub-owned remote publication. The chain is:

```text
release/version.sdn  --render/check-->  projections (VERSION, simple.sdn, Cargo.*, ...)
        |
        v
ReleasePlan  --VersionDecision(fail-closed)-->  ReleaseCandidate (candidate/<ver>/<id>)
        |                                              |
        v                                              v
ReleaseLine (release/X.Y, support_state)     GateBundle @ exact RevisionId
                                                       |
                       SJ create_release_tag (signed, create-fails-if-exists)
                                                       |
                       DevHub ReleaseProvider draft -> assets -> publish -> verify
                                                       |
                                    Release (immutable) -> Publication records
```

Measured seams: `release/version.sdn` exists (schema
`simple-release-version/1`, 10 compatibility axes, declared projections);
`src/app/devhub/version_manifest.spl:114-244` parses, renders, and reports
projection drift and undeclared consumers; `ReleaseLine`/`ReleaseCandidate`/
`ReleaseIdentity`/`Publication` are value objects at `model.spl:161-204`;
`release.spl:6-27` enforces candidate abandon vs published withdraw.

Architectural rules (doc 2 §7.5-7.6, doc 1 §9.5-9.6):

- Tag creation fails if the name exists; no force update in published tag
  namespaces; candidates use `candidate/*` refs, never tags.
- The version bump is an output of `ReleasePlan` plus explicit approval, never
  the first action. For a stable release, "analysis did not run" is FAIL, not
  "no breaking change".
- Publication authority requires: complete exact-revision gate bundle,
  release-profile approval, deterministic tag/artifact identity, configured
  human or protected automation authority, remote CAS still matching the
  candidate, no unresolved critical finding, no unforwarded emergency fix.
- A published release is immutable; corrections create a new version.
  Release-line support (`planned -> maintained -> security_only -> end_of_life`)
  lives on `ReleaseLine.support_state`, not on the release.
- Backport is an explicit `BackportRecord` per maintained line (doc 1 §7.3-7.4);
  the release line is never merged back into `main`.

### Stage 4 — DevHub provider projection

Providers advertise **capability records** (`ProviderCapabilities`,
`src/app/devhub/provider/lifecycle_capability.spl:16-24`) and DevHub selects
operations by capability, never by lowest common denominator. A local blocking
verdict is never projected as a non-blocking provider comment
(`provider_review_operation`, `:26`, strict-sync refuses). Every remote link is
a `RemoteBinding` (`model.spl:102`) with a sync base; sync is field-level
three-way (`sync.spl:30`), never timestamp last-write-wins; conflicts persist
(`sync.spl:72`) and are never auto-overwritten. Outbound events go through the
idempotent CloudEvents-shaped outbox (`sync.spl:16-28`). GitHub is the first
projection; adapters live under `src/app/devhub/provider/<name>/` and call the
existing `src/app/devhub/adapter_*.spl` transports.

### Stage 5 — features, tasks, and wiki

Work graph and change graph are separate (doc 1 §5.7): `Feature -> Task ->
LifecycleRun -> Change`, validated by `work.spl:7-19`. Durable feature manifests
live in `doc/08_tracking/feature/<FeatureId>/feature.sdn`; runtime agent
progress stays in `.spipe/run/<run-id>/state.sdn` and is never a lifecycle
entity. Field authority is per binding (`local_first | remote_first |
field_split | mirror`, doc 1 §17.3); wiki pages have a local managed region
and a remote unmanaged region.

### Stage 6 — provider expansion (6a) and policy compilation (6b)

6a adds GitLab, Gerrit, Review Board, then Bitbucket typed completion, each
against the same provider contract suite; unsupported semantics fail
explicitly and no provider logic enters Spipe skills. 6b makes
`.spipe/policy/*.sdn` normative and generates skills, rules, guide tables and
gate entries from it, failing closed on drift. Design carries both.

### Stage 7 — SCV content-authority promotion

Vocabulary reconciliation (decision): doc 2 authority modes map onto the SCV
migration gates — Mode A `git_jj_scv_shadow` = today (S0 observe); Mode B
`dual_verified` = the S4 ceiling of
`doc/03_plan/app/tools/scv_migration_month_plan.md`; Mode C `scv_native` =
S5/S6, outside the month window. Promotion gates are defined by that plan
(signed step scripts, `PASS` last-line verdicts) and are not restated here.
Git/JJ rollback remains available until final promotion. The forbidden
topology (doc 2 §4.4, three raw mutators on one workspace) is rejected by the
gateway once enforcement is enabled.

## Verdict discipline

Every lifecycle command, planner, and gate returns one of three distinct
outcomes: PASS (something was checked and admitted), FAIL (checked and
rejected, naming the offender), ERROR — nothing was checked (missing policy,
missing binary, empty range). A vacuous run is never a pass; `LifecycleResult`
(`model.spl:206`) carries `ok/status/code` so callers cannot collapse the three.

The initial policy is observe-only. Promotion to local integration, remote
publication, signed tags, or SCV content writing is a separate policy change
requiring stage exit evidence.
