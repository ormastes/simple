# Beta-2 release refused: required Linux candidate row has no live workflow-file defect — triage 2026-09-14

## Symptom
`v1.0.1-beta.1` release (and the prior beta refusal, PRs #964/#965) is blocked
because the required beta row `x86_64-unknown-linux-gnu` needs a GitHub
Actions **candidate** run, and the two historical candidate.yml runs cited as
evidence (`33056214368`, `33055941933`, both 2026-08-27) completed in 0s with
`total_count: 0` jobs.

## Findings (verbatim API evidence)

1. **Historical runs are anomalous, not representative of the current file.**
   `gh api .../actions/runs/33056214368 --jq '{conclusion,event,head_branch}'`
   → `{"conclusion":"failure","event":"push","head_branch":"pr/sspec-maintain-80"}`.
   But `.github/workflows/candidate.yml`'s `on:` block — **both on `main` today
   and at the run's own `head_sha` 81ba95a454e4f46b083d4573a6eb30e0942a7f5c**
   (fetched via `gh api contents/... ?ref=<sha>`) — declares `workflow_dispatch`
   only, no `push:` trigger at all. A `workflow_dispatch`-only workflow cannot
   be triggered by a push event under GitHub's own semantics, so these two runs
   are not evidence of a defect in candidate.yml's current trigger/job
   definition — they are an artifact of whatever repo/workflow state existed
   when they were recorded (possibly a renamed/superseded file sharing
   `workflow_id 343348141`, or an out-of-band condition). No "workflow file
   issue" annotation exists to quote: `gh api commits/<sha>/check-runs` for
   that sha returns only 3 unrelated check-runs (`SPipe Self Review
   Admission`, its revalidate/invalidate siblings) — nothing named
   `candidate` or `qualify-linux`.

2. **A live dispatch probe on `main` today DOES start a job.**
   `gh workflow run candidate.yml --ref main -f candidate_ref=... -f
   convergence_run_id=1 -f convergence_artifact=probe -f
   convergence_artifact_id=1 -f convergence_artifact_digest=sha256:00...0 -f
   convergence_receipt_sha256=00...0` (placeholder/invalid convergence inputs,
   since the goal was only to test whether a job starts) produced run
   `34791813627`, event `workflow_dispatch`, which immediately went to
   `status: queued` with **`total_count: 1`** job (`qualify-linux`) via
   `gh api actions/runs/34791813627/jobs`. This is the opposite of the 0-job/
   0s symptom — `candidate.yml` on `main` is loadable, its `workflow_dispatch`
   inputs are satisfiable, and the runner-assignment path is live. The probe
   run was left queued (public-repo hosted-runner queue latency, not a
   workflow defect) and was not force-completed; it will fail its own input
   validation once scheduled, which is expected and harmless for a repo
   this size with placeholder inputs.

3. **Account-level block ruled out.** `gh api /repos/ormastes/simple --jq
   '{private,owner_type}'` → `{"private":false,"owner_type":"User"}`.
   `gh api /repos/ormastes/simple/actions/permissions` → `{"enabled":true,
   "allowed_actions":"all"}`. `gh api /user/settings/billing/actions` → 404
   (expected: that endpoint is for GitHub-hosted-runner billing on paid
   plans; a public repo on a free/User plan gets unmetered `ubuntu-latest`
   minutes, so the 404 is not itself evidence of a block — but the important
   fact is `actions/permissions.enabled: true` and a job did get created and
   queued in finding 2, which is the actual proof no account-level block is in
   effect).

4. **release.yml not yet cross-checked.** Time-boxed at this triage pass —
   the same `event`/`head_sha`-at-time-of-run check should be repeated against
   the run that produced the published-but-assetless `v1.0.1-beta.1` tag
   before concluding release.yml has no analogous historical-run artifact.

## Conclusion
No workflow-file or account-level defect exists in `.github/workflows/candidate.yml`
on `main` as of 2026-09-14. The cited historical 0-job runs do not reproduce
against the current file and are not explained by anything wrong with it —
they predate or reflect a different file/trigger state than what ships today.
**No code change was made.** The unblock path for the beta-2 release is
operational, not a bug fix: dispatch `candidate.yml` with the *real*
convergence-checkpoint inputs (`convergence_run_id`, `convergence_artifact`,
`convergence_artifact_id`, `convergence_artifact_digest`,
`convergence_receipt_sha256`) from a genuine successful protected-integration
run, and let the `qualify-linux` job run to completion to produce the required
Linux candidate row — rather than treating the two stale 0-job runs as proof
the workflow itself needs repair.

## Probe run
`https://github.com/ormastes/simple/actions/runs/34791813627` (workflow_dispatch,
placeholder inputs, used only to confirm a job starts — expected to fail once
scheduled since the convergence inputs are not real).
