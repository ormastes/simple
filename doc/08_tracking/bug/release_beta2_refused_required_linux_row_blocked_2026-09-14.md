# Release refused 2026-09-14 — beta required row `x86_64-unknown-linux-gnu` is `blocked`, and the candidate/release CI route has never succeeded

Session: `work/release-2026-09-14`, worktree `.claude/worktrees/agent-ab81388b5fde969c4`,
base `a7a19a52182` (= `origin/main` at start). Host: macOS aarch64.
Directive: "do local and remote release" (local release + tag push + GitHub release).

**Verdict: NO tag was created and NO GitHub release was published.** The refusal comes
from the release admission contract itself (`doc/07_guide/infra/software_release.md`,
`release/support.sdn`), not from operator caution. The guide states bug/support
requirements have "no waiver", so the user's push authority cannot substitute for a
missing required-platform receipt.

## Identity that a release would have had to use

- `release/version.sdn` canonical semver: **1.0.1-beta.1**, line `1.0`, channel `beta`.
- `git tag --list 'v*' | sort -V | tail`: `v0.9.8`, `v1.0.0-RC`, `v1.0.0-beta`,
  **`v1.0.1-beta.1`** (annotated; `git cat-file -t` = `tag`), `vgate-probe-004312`.
- `gh release list`: **`v1.0.1-beta.1` is already published** (pre-release,
  2026-09-06T23:49:50Z). Published identity is immutable and tags are immutable by the
  `spipe-vcs-v3-version-tags` ruleset, so `v1.0.1-beta.1` must not be reused or moved.
- Therefore any new work requires a **new** identity: **`1.0.1-beta.2`**.
  `release/version.sdn` still reads `1.0.1-beta.1` and is stale relative to what is
  published; a beta.2 would need a `version-bump` + projection PR first.

## Checker verdicts (verbatim)

Run with the seed's `run` (`bin/simple run src/app/release/main.spl <cmd>`) because the
bootstrap CLI has no `release` subcommand. The seed is used here only to *execute a pure-Simple
checker*, never as release evidence.

```
Release version-check: PASS
```

```
{"output_version":"simple-release/v1","command":"release support-check","status":"ok","channel":"beta",
 "required_support":[{"target":"x86_64-unknown-linux-gnu","tier":"tier_1","runner":"ubuntu-latest",
   "bootstrap":"full","whole_tests":"required","status":"passed"}],
 "support_matrix":[{"target":"x86_64-unknown-linux-gnu","tier":"tier_1","runner":"ubuntu-latest",
   "required":true,"availability":"supported","bootstrap":"full","whole_tests":"required",
   "status":"blocked"},
  {"target":"aarch64-unknown-linux-gnu","tier":"experimental","runner":"self-hosted",
   "required":false,"availability":"experimental","bootstrap":"full","whole_tests":"required",
   "status":"experimental"}]}
```

```
{"output_version":"simple-release/v1","command":"release candidate-check","status":"rejected",
 "reason":"candidate version is invalid"}
```

```
{"output_version":"simple-release/v1","command":"release promote-check","status":"rejected",
 "reason":"release mutation requires a session id and workspace"}
```

## Why this is a hard blocker, not a paperwork gap

1. **The one required beta target is `blocked`.** `release/support.sdn` declares exactly one
   `required: true` row per channel (`check_single_job_coverage` enforces one), and for `beta`
   that row is `x86_64-unknown-linux-gnu`. The live support matrix reports it
   `"status":"blocked"`. The guide: "Only actually executed required rows may say `passed`; a
   missing required receipt blocks admission."
2. **This host cannot supply that row.** The session host is macOS aarch64. The binary the
   bootstrap lane (F74) is deploying is `aarch64-apple-darwin-macho`, which is **not a declared
   row at all** in `release/support.sdn`. The guide forbids exactly this substitution: "No lane
   may substitute a seed, source-only, or foreign-target fallback artifact for a missing native
   result." A macOS whole-suite PASS is genuine evidence for an undeclared target; it is not the
   required Linux receipt.
3. **The CI route that *would* produce that row has never worked.**
   - `gh run list --workflow=candidate.yml -L 5`: five most recent runs are **all
     `completed failure`, each `0s`** (latest 2026-08-27). There is no successful
     `Build and qualify immutable candidate` run, hence no `simple-release-candidate/1` /
     `simple-release-admission/1` evidence in existence.
   - `gh run list --workflow=release.yml -L 5`: **all `completed failure`**, including run
     `34067963746` for tag `v1.0.1-beta.1` itself (4h53m52s, failure, 2026-09-06).
   - Consistent with that, **`gh release view v1.0.1-beta.1` lists zero assets** — the published
     beta.1 release carries no admitted artifacts. So the already-published beta.1 did not go
     through a completed promotion either.
4. **No admitted candidate exists to promote.** `promote-check` requires "an admitted candidate
   identity and exact commit" plus "exact matching artifact/evidence manifests". Nothing has ever
   been admitted (point 3), so promotion has no input and correctly rejects.
5. The guide's own § *Current verification boundary* already records this state: "The exact
   release lineage still lacks admitted Stage 3 and Stage 4 receipts and one clean release-grade
   `bin/simple test test --whole --mode=interpreter` PASS. No signed beta tag, immutable candidate
   publication, or byte-identical npm publication receipt exists." That paragraph is still
   accurate, with the one correction that a tag named `v1.0.1-beta.1` *was* subsequently pushed
   and a GitHub release published — asset-less, over a failed `release.yml` run.

## Release-bound whole-suite test: not run, dependency never arrived

The directive bound the release to ONE `bin/simple test test --whole --mode=interpreter` PASS on
the self-hosted full-CLI binary being deployed by the F74 bootstrap lane.

- `bin/simple` resolves to the **Rust seed** (`target/bootstrap.generations/502da3d0…/simple`),
  which prints `WARNING: this Rust-built Simple binary is a bootstrap seed only` and reports
  `Simple Language v1.0.0-rc.1`. The seed is bootstrap-only and is not release evidence.
- `bin/release/aarch64-apple-darwin-macho/simple` is dated **Sep 7 16:38**, i.e. the pre-existing
  artifact, not a fresh F74 deploy.
- Last F74 status lines observed:

  ```
    (pid 67477 = stage2-admitted compiler, 58 min CPU, 23%, compiling src/app/cli/bootstrap_main.spl
     -> stage3/aarch64-apple-darwin/simple). The resume path pins --threads 1, so 60 min was an
    under-estimate, not a hang. NOT killed: killing a live build is exactly what cost the last two lanes.
  ```

  The lane is still building **Stage 3**; Stage 4 / full-CLI relink has not started.

Even had it landed, per §2 above a macOS-arm64 PASS could not admit this release. It would be
recorded as evidence for an undeclared target.

## What a legitimate `1.0.1-beta.2` needs

1. Repair `.github/workflows/candidate.yml` so it completes on `ubuntu-latest` (its runs fail at
   0s, i.e. before doing work — triage that first). Without a green candidate run there is no
   admitted artifact for any channel.
2. `version-bump` to `1.0.1-beta.2` and land the 17 `projections:` from `release/version.sdn`
   through a PR (protected `main`, PR-only).
3. Create the create-once candidate ref, let `candidate.yml` build and qualify the required
   `x86_64-unknown-linux-gnu` row with full bootstrap + whole-test receipts.
4. Obtain `spipe-review-admission/1` (or the documented owner-attested fallback), then
   `candidate-admit`, then `promote-check`, then let `release.yml` sign the single tag and attach
   the admitted assets unchanged.

Steps 3-4 cannot be performed from this macOS host; they are CI-side.

## Raw logs

`build/release-evidence/{support-check,candidate-check,promote-check}.log`
and `candidate-check.json.log` (untracked; session-local).

## Two honesty notes on the verdicts above

- **`candidate-check` / `promote-check` were invoked with no arguments**, so their rejections are
  *precondition* failures (no candidate manifest exists; no session is registered), not the support
  contract refusing. They are quoted verbatim but must not be read as the discriminating verdict.
  The discriminator is `support-check` + the zero successful `candidate.yml` runs.
- **`support-check` contradicts itself and this is a checker defect.** For the same target,
  `required_support[0].status` renders `"passed"` while `support_matrix[0].status` renders
  `"blocked"`. No required-row receipt exists, and the guide says only an actually-executed
  required row may say `passed` — so `required_support` is emitting `passed` from nothing. A
  reader looking only at `required_support` would wrongly conclude the row is satisfied. Fix in
  `src/app/release/support_policy.spl`.

---

## Triage round 2 (2026-09-14) — re-landed from closed PR #966 plus new runner evidence

PR #966 carried this triage but its branch was deleted before merge; the
findings are re-landed here.

### A. No workflow-file defect in `candidate.yml`
The two historical candidate runs cited as evidence (`33056214368`,
`33055941933`, both 2026-08-27) completed in 0s with `total_count: 0` jobs and
`event: "push"` / `head_branch: "pr/sspec-maintain-80"`. But `candidate.yml`'s
`on:` block — **both on `main` today and at that run's own `head_sha`
`81ba95a454e4f46b083d4573a6eb30e0942a7f5c`** (fetched via
`gh api contents/...?ref=<sha>`) — declares `workflow_dispatch` only, with no
`push:` trigger. A `workflow_dispatch`-only workflow cannot be triggered by a
push, so those runs do not reflect the file that ships today. No
"workflow file issue" annotation exists to quote:
`gh api commits/<sha>/check-runs` returns only 3 unrelated check-runs
(`SPipe Self Review Admission` and its revalidate/invalidate siblings).

### B. No account-level block
- `gh api /repos/ormastes/simple --jq '{private,owner_type}'` →
  `{"private":false,"owner_type":"User"}`
- `gh api /repos/ormastes/simple/actions/permissions` →
  `{"enabled":true,"allowed_actions":"all"}`
- `gh api /user/settings/billing/actions` → 404 (that endpoint is for
  hosted-runner billing on paid plans; a public repo on a User/free plan gets
  unmetered `ubuntu-latest` minutes, so the 404 is not evidence of a block).

### C. A live dispatch probe DOES create a real `qualify-linux` job
`gh workflow run candidate.yml --ref main` with placeholder convergence inputs
produced run
`https://github.com/ormastes/simple/actions/runs/34791813627`
(`event: workflow_dispatch`). `gh api actions/runs/34791813627/jobs` →
`total_count: 1`, job `qualify-linux`, `labels: ["ubuntu-latest"]`,
`status: "queued"`, `runner_name: ""`, `steps: 0`. It was left queued and not
force-completed; it will fail its own input validation once scheduled, which is
expected and harmless with placeholder inputs.

### D. GitHub-hosted runners DO pick up this repo's jobs — verbatim evidence
The decisive question of round 2 was whether any job in this repo has ever
started on a GitHub-hosted runner. It has, minutes before the probe:

```
gh api /repos/ormastes/simple/actions/runs/34790945536/jobs
{"completed_at":"2026-09-14T00:01:05Z","conclusion":"success",
 "labels":["ubuntu-latest"],"name":"publish",
 "runner_group_name":"GitHub Actions",
 "runner_name":"GitHub Actions 1000436809",
 "started_at":"2026-09-13T23:59:40Z","steps":8}
```

A real hosted runner (`GitHub Actions 1000436809`) was assigned, executed 8
steps and succeeded. **The account-side hypothesis (Actions minutes exhausted,
runners disabled for public repos, or a pending first-time-contributor
approval) is therefore falsified** — none of those would allow that job to run.

### E. The actual cause of the probe's wait: repo-side queue saturation
```
gh api '/repos/ormastes/simple/actions/runs?status=queued&per_page=1' --jq .total_count      -> 90
gh api '/repos/ormastes/simple/actions/runs?status=in_progress&per_page=1' --jq .total_count ->  4
```
90 queued runs against 4 in progress. The probe is FIFO-queued behind that
backlog, against the free-tier hosted-runner concurrency cap. This is a
throughput condition that drains on its own, **not** an account-side block and
**not** a condition the repository owner must act on to re-enable Actions.

### F. Ordering correction for the beta-2 flow
`candidate.yml`'s first step validates
`candidate_ref` against
`^candidate/v[0-9]+\.[0-9]+\.[0-9]+(-(alpha|beta|rc)\.[0-9]+)?/a[0-9]{3}$`
and then checks that ref out. A candidate qualified from today's `main` (still
`1.0.1-beta.1` in `release/version.sdn`) therefore cannot serve `beta.2`. The
correct order is: **version-bump PR to `1.0.1-beta.2` → merge → create the
immutable `candidate/v1.0.1-beta.2/aNNN` ref at that commit → dispatch
`candidate.yml` against that ref** with the real convergence-checkpoint inputs.
Dispatching before the bump wastes a full trip through the queue.

### G. The REAL blocker is one layer deeper, and it is owner-authority, not CI

Section E answers "can a runner start?" (yes). But `candidate.yml`'s
`qualify-linux` cannot be *legitimately* dispatched at all, because its five
required `convergence_*` inputs describe an artifact that has never existed.

**G.1 — the receipt producer has never run, not once.**
The only workflow that builds `convergence-receipt.json` /
`convergence-receipt.sha256` and uploads it as
`convergence-receipt-<CANDIDATE_COMMIT>` is
`.github/workflows/pr-admission.yml` (`name: Protected integration convergence
admission`; artifact name computed at :76, receipt at ~:671, attested via
`attest-build-provenance`). `candidate.yml:211` hard-requires
`test "$RECEIPT_ARTIFACT" = "convergence-receipt-${COMMIT}"`.

```
gh api /repos/ormastes/simple/actions/workflows/pr-admission.yml/runs --jq .total_count
-> 0
```

All five inputs derive from that non-existent run:
`convergence_run_id` (no run id), `convergence_artifact` (shape known, no
instance), `convergence_artifact_id` / `convergence_artifact_digest` (assigned
by GitHub at upload; no upload occurred), `convergence_receipt_sha256`
(computed inside the producer at :678, echoed only to `GITHUB_OUTPUT`, never
persisted). No `convergence-receipt.json`/`.sha256` is checked into the tree.
`candidate.yml` itself has 35 runs: 34 `failure`, 1 the queued probe — zero
successes. The sibling `release-convergence-checkpoint.yml` is a *different*,
read-only observer (`release-convergence-checkpoint-<run_id>`, not the receipt)
and its last 50 scheduled runs through 2026-09-13 18:27Z are all
`failure`/`cancelled`.

**G.2 — the producer's own preconditions are absent.**
`pr-admission.yml` is `workflow_dispatch`-only and requires `release_ref`
(a protected maintenance line `release/X.Y`), `candidate_commit_sha`,
`integration_pr_number` (an exact *merged* integration PR into that line), and
`authority_class`.

```
gh api '/repos/ormastes/simple/branches?per_page=100' --jq '[.[].name]|map(select(startswith("release")))'
-> []
```

No `release/*` branch exists, so there is no maintenance line and no merged
integration PR into one. (The ruleset `spipe-vcs-v3-release-lines` already
exists to protect such a branch once created.)

**G.3 — the approval path is provably circular (the decisive finding).**
`pr-admission.yml`'s job runs in
`environment: ${{ inputs.authority_class == 'owner_attested_actions' &&
'owner-convergence-admission' || 'protected-integration' }}`.

```
gh api /repos/ormastes/simple/environments --jq '[.environments[].name]'
-> ["npm-release","protected-integration","release","self-review-admission"]

gh api /repos/ormastes/simple/environments/protected-integration \
  --jq '[.protection_rules[]|select(.type=="required_reviewers")|{prevent_self_review,reviewers:[.reviewers[].reviewer.login]}]'
-> [{"prevent_self_review":true,"reviewers":["ormastes"]}]
```

- Default lane (`external_broker` → `protected-integration`): the sole required
  reviewer is `ormastes`, who is also the sole repository owner, and
  `prevent_self_review` is `true`. The owner therefore **cannot approve their
  own dispatch**. The guide states this in its own words at
  `doc/07_guide/infra/software_release.md:323-325`: *"The declared environment
  reviewer is also the sole repository owner, so GitHub `prevent_self_review`
  still makes the release-environment path circular."*
- Fallback lane (`owner_attested_actions` → `owner-convergence-admission`): the
  guide at :200-203 says that environment *"requires owner ID `2378857` and has
  `prevent_self_review=false`"* — but **that environment does not exist on the
  live repository** (see the 4-name list above). Only the source projection
  `.github/owner-convergence-admission-environment.json` exists, and guide
  :331-334 is explicit that *"The source projection is not live evidence until
  the repository policy owner runs that command"*.

So both lanes are closed: one is circular by GitHub's own self-review rule, and
the one designed to break the circle has never been applied to the repository.

## Unblock — required repository-owner actions (no agent can perform these)

1. Configure the external policy DB secret, then run
   `scripts/release/github-policy.shs apply-live --yes` as the repository policy
   owner, and retain its post-apply receipt + projection digest. This is the
   documented command (guide :326-334) that turns the `.github/*-environment.json`
   projections into live configuration — including creating the
   `owner-convergence-admission` environment with `prevent_self_review=false`
   and owner ID `2378857`, which is what makes the fallback lane usable at all.
2. Create the protected maintenance line `release/1.0` at the intended target
   commit (the `spipe-vcs-v3-release-lines` ruleset already covers `release/*`),
   and land the protected-integration PR into it, recording its exact merged PR
   number and merge commit SHA.
3. Dispatch `pr-admission.yml` with `release_ref=release/1.0`, that
   `candidate_commit_sha` and `integration_pr_number`, and either
   `authority_class=external_broker` (requires a second human reviewer distinct
   from the dispatcher — impossible while `ormastes` is the sole owner) or, once
   step 1 has created the environment, `authority_class=owner_attested_actions`
   with `owner_attestation=NO-VERIFY:OWNER-PROOF` dispatched from trusted `main`,
   together with the verifier-unavailability proof the receipt must retain.
4. Approve the resulting environment deployment gate in the GitHub UI. **This
   approval must not be performed programmatically by an agent via
   `actions/runs/<id>/pending_deployments`** — it is the human control the whole
   admission design rests on.

Only after step 4 produces a *successful* `pr-admission.yml` run do the five
`convergence_*` values exist, at which point the beta-2 flow can proceed in the
order established in section F (version bump → merge → immutable candidate ref →
`candidate.yml` dispatch → `candidate-check` → `promote-check` → `release.yml`).

## Conclusion (supersedes the earlier conclusion above)

Two distinct things were confounded and are now separated:

- **Not a blocker:** the workflow file, Actions being enabled, hosted-runner
  availability, or Actions minutes. Section D proves a hosted runner executed a
  job successfully minutes before the probe; section E shows the probe's wait is
  ordinary queue saturation (90 queued / 4 in progress) that drains on its own.
- **The blocker:** the convergence-admission chain has never been established —
  no `release/*` line, no integration PR into one, the receipt producer has zero
  runs, and both of its approval environments are unusable (one circular under
  `prevent_self_review`, the other not created on the live repository).

Round 2 therefore made **no** version bump, created **no** candidate ref,
dispatched **no** real candidate run, and cut **no** tag. `v1.0.1-beta.1` was
not touched. `bin/simple run src/app/release/main.spl version-check` was run and
reported `Release version-check: PASS` at `1.0.1-beta.1`, confirming the local
release tooling is healthy and that the bump itself is a small, deferrable step
once the chain above is open. Landing the version bump now would leave `main`
claiming a version that can never be tagged, so it was deliberately not done.
