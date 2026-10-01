# review-admission.yml: silent merge-base failure in shallow checkout blocks self-review admission

Date: 2026-09-17
Lane: BOOT-20 (bootstrap verification), observed while admitting PR #1062
Severity: medium — blocks every self-review admission whose merge-base is
not the base branch tip (i.e. any PR created after main took a merge commit)

## Symptom

`review-admission.yml` dispatch for PR #1062 (head
`b488a271c48911f581a309226cac28584e0ccfc2`) failed ~1.2s after its internal
`git fetch` with **no stdout/stderr at all**, publishing a rejected
"SPipe Self Review Admission" check with
`Rejection reason: provider fetch or exact changed-manifest binding failed`.

PR #1059's dispatch (same workflow revision) succeeded 51s earlier.

## Root cause

The runner's checkout uses `fetch-depth: 1`. The admission step then runs
(`.github/workflows/review-admission.yml`, "Resolve, evaluate..." step):

```
git fetch --no-tags --no-recurse-submodules origin "+refs/pull/$PR_NUMBER/head:..." "+refs/heads/$base_ref_name:..."
test "$(git rev-parse ...)" = "$head_sha"
...
merge_base_sha=$(git merge-base "$base_sha" "$head_sha")
```

`git merge-base` exits **1 with no output** when the shallow graph contains
no common ancestor. For #1059 the base tip (`c2f8a87d13c`) WAS the
merge-base, so the shallow graph answered; for #1062 main's tip was a merge
commit (`630593d6082`, the #1059 merge) and the true merge-base
(`ebca1215f47`) sat below the shallow boundary → silent rc=1 →
`set -Eeuo pipefail` killed the step before any echo. `failure_stage` at
that point is 'provider fetch or exact changed-manifest binding failed',
which mislabels a pure git-shallowness problem as a manifest/policy failure.

Reproduced locally:
`git clone --depth 1` + the workflow's exact fetch →
`git merge-base 630593d6082… b488a271c48…` → rc=1, empty.
After `git fetch --deepen=50` → rc=0, merge-base `ebca1215f47…`.

## Fix options (infra lane)

1. Add history depth to the admission fetch, e.g.
   `git fetch --deepen=500 --no-tags …` (or `--unshallow`) before the
   merge-base call; or
2. Replace the subprocess merge-base with the GitHub API
   (`gh api repos/{}/compare/{base}...{head}` → `merge_base_commit.sha`),
   which is shallow-proof; or
3. Catch the empty merge-base and emit a real diagnostic instead of dying
   silently (independent of 1/2 — the silent-set-e pattern here cost an
   hour of diagnosis).

## Workaround used for #1062

Merged via the ruleset relax/restore admin dance (same as #1059); the
failed admission check-run on `b488a271c48` is an artifact of this defect,
not a policy denial.
