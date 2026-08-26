# Protected beta and stable software release

> Manually synchronized with the executable SSpec after the final hardening
> changes. Doc generation was not rerun because this lane had reached its
> three-cycle retry cap. The runnable source remains authoritative.

## At a glance

| Property | Rule |
|---|---|
| Authoring | One registered session, one `work/*` branch, one linked worktree |
| Beta fixes | One exact reviewed fix at a time; no automatic cherry-pick |
| Trunk | `main` remains the independent development trunk |
| Candidate | Create once; exact candidate/qualification/admission identities |
| Promotion | Signed annotated exact tag; admitted assets; no rebuild/fallback |
| npm | Candidate-built admitted tarballs are published unchanged |
| Recovery | Retry idempotently, redeploy, withdraw, or issue a new version |

## Requirements and sources

- Requirements: `doc/02_requirements/feature/release_process_hardening.md`
- NFRs: `doc/02_requirements/nfr/release_process_hardening.md`
- Architecture: `doc/04_architecture/release_process_hardening.md`
- Design: `doc/05_design/release_process_hardening.md`
- Test plan: `doc/03_plan/sys_test/release_process_hardening.md`
- Runnable scenario: `test/03_system/app/release/feature/release_process_hardening_spec.spl`

## Operator flow

### 1. Load the canonical release policy

Read `release/version.sdn`, verify its deterministic projections, and reject
stale or undeclared product-version consumers. New prereleases are lowercase
and numbered, such as `1.4.0-beta.2`.

### 2. Prepare an isolated beta release

Work only from a linked non-main worktree on a unique `work/*` branch. The
trusted authority verifies canonical paths, Git worktree/branch/HEAD/target
state, and the VCS-policy digest. Register the session under the repository-wide
lock before a mutating command. Duplicate session, workspace, or branch
ownership and stale, detached, protected, symlink-aliased, or unregistered
sessions fail closed. Outputs and writable cache overlays are session-private.

### 3. Admit reviewed bug-fix backports

An admissible `main`-to-beta fix binds one exact source SHA, stable change/work
IDs, `kind=fix`, exact source review, exact target head, explicit adaptation
reason, result SHA, and renewed result evidence. A feature, range, moving ref,
stale review, or pre-application evidence is rejected.

For a release-first emergency fix, the same contract requires an exact reviewed
forward-port receipt targeting `main`. A release-only compatibility change may
remain divergent only with an explicit reviewed reason.

### 4. Inspect main/release convergence

At bounded bootstrap or beta checkpoints, fetch exact `main` and `release/X.Y`
heads and compare no more than 256 source-only commits. Discovery is fetch-only:
it never selects, applies, merges, or pushes. A caller explicitly selects exact
review-bound fixes; each must be reachable from the source and absent, including
patch equivalence, from the target.

After protected CAS integration, record a divergence receipt only when a fresh
fetch proves the source unchanged, the target append-only and equal to the
reviewed result, and every selected patch represented. `main` must remain a
separate development trunk and must never track, reset to, or be replaced by the
release line. For `release_to_main`, the release source head must not become an
ancestor of the resulting `main`; that graph shape is a forbidden whole-line
merge even when the two heads differ.

Candidate admission recomputes the complete release-only inventory at the
manifest's exact pre-administration boundary; only manifest changes may follow
that boundary before the integration merge. Every selected `main` fix must name
a result in that release inventory, match it by stable patch ID, and carry the
exact release PR review/check receipt; candidate CI replays every source/result
binding. Every release-only row must have an aligned
`fix` or `non_fix` classification receipt. Every `fix` row must additionally
name a result already represented on `main`, match it by stable patch ID, and
carry an exact main-targeted forward-port receipt. Every `non_fix` row requires
a reason, owner, and future RFC 3339 expiry. Named successful provider checks
must match the configured check name and GitHub App identity. A nonempty
inventory paired with an empty classification list is rejected.

The executable scenario covers both reviewed directions. A `main` fix produces
a mutation-free backport plan; a release-first fix requires an explicit
forward-port target of `main`; concealed release-only inventory and any plan
claiming that `main` tracks or absorbs the release line are rejected.

### 5. Freeze and qualify the candidate

The first beta candidate is `candidate/v1.4.0-beta.2/a001`. The canonical
`simple-release-candidate/1` identity binds version, attempt, ref, exact commit,
source tree, policy, version manifest, toolchain, support manifest, build graph,
creator, and evidence identities. Identical retry is idempotent; different
content at the same identity is rejected.

Qualification binds the artifact and required-support manifests to that
candidate. Admission additionally binds the qualification and convergence
receipts and asserts `required_support_passed=true`, `admitted=true`,
`rebuild_allowed=false`, and `fallback_used=false`.

Candidate CI builds the compiler/package assets once, runs the required
bootstrap and whole-test gates, generates checksum/SBOM/provenance evidence,
and packs the MCP and LSP MCP npm tarballs. Those `.tgz` files are admitted
release assets, not recreated by publication.

### 6. Promote exact admitted artifacts

Promotion verifies the successful candidate workflow run, exact candidate ref
and commit, every manifest digest, required support, provenance, and immutable
release configuration. It creates or verifies one signed annotated `v...` tag
and pushes only that exact ref.

A retry accepts an existing tag only when signature, commit, and admission
digest match. It resumes an existing draft, rejects unadmitted remote assets,
compares bytes for existing assets, uploads only missing admitted assets, checks
the final exact asset set, and verifies the immutable published release. It does
not compile, package, rewrite versions, or use fallback content.

The npm workflow downloads and verifies the admitted tarball, then publishes
that file with `alpha`, `beta`, `rc`, or `latest`. An already-existing registry
version is idempotent only when its packed bytes and distribution tag match.

### 7. Withdraw without rewriting release identity

Rollback redeploys a prior admitted version. Withdrawal preserves tags, assets,
and audit history. A correction receives a new beta, RC, or patch identity.

## Executable scenario coverage

The runnable SSpec currently contains seven active scenarios and no placeholders:

1. canonical policy/version parsing and stale projection rejection;
2. isolated beta preparation and main-worktree rejection;
3. reviewed backport/forward-port admission and feature/stale-review rejection;
4. mutation-free bidirectional convergence planning and independent-trunk rejection;
5. complete candidate and qualification receipt plus create-once rejection;
6. exact admission/promotion plus rebuild and version/tag mismatch rejection;
7. non-destructive withdrawal.

Trusted session registration and Git convergence require real repository
fixtures and are covered by their focused integration specs rather than being
faked in this pure system scenario.

## Current evidence boundary

This manual does not claim a live beta release. Live GitHub policy verification
now passes for seven rulesets, the declared environments, and immutable release
configuration. Stage 3/4 qualification, one clean release-grade whole-suite
confirmation, an exact signed beta promotion, immutable publication of that
candidate, and byte-identical npm publication still require receipts. Missing
release evidence is a release-blocking FAIL, never a degraded PASS.
