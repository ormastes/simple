# Landing a PR on `main` is a timing race, not a checklist

The mechanics of opening and merging a protected PR are already written down and
are not repeated here:

- `.claude/rules/vcs.md` § Push/land — the push/`gh pr create`/`gh pr merge`
  recipe, the two required checks, the `opened`-is-not-in-`pull_request_target`
  trap, and the "push only YOUR commit" scope rule.
- `.claude/skills/spipe.md` — the `gh workflow run review-admission.yml`
  dispatch, the two admission traps (a byte-identical `--body-file` fires no
  `edited` event; repeated edits cancel the workflow's own in-flight run), and
  the user-authorized emergency ruleset bypass.

This page covers only what those two do not: **why a correct recipe still fails
repeatedly, and the loop that gets around it.**

## Why it is a race

Three properties compose into one:

1. **The ruleset requires two checks with strict up-to-date.** `Code Idiom &
   Structural Ratchet Gates` (`.github/workflows/repo-hygiene.yml`) runs
   automatically on `pull_request`. `SPipe Self Review Admission`
   (`.github/workflows/review-admission.yml`) does **not** — on a
   `pull_request` its job is skipped, and the dispatch path is
   `workflow_dispatch` only.

   Per `.claude/rules/vcs.md` and `.claude/skills/spipe.md`, the *normal* path
   is that a genuine `edited`/`synchronize` event creates the check-run as
   **skipped**, and GitHub's rollup accepts a skipped required check — that is
   how PRs land routinely. Measured 2026-09-06 that did not happen: the gate
   sat `expected`/`queued` with no satisfying run, and only a dispatch cleared
   it. So do not assume either behaviour. Read `gh pr checks <n>`: if admission
   is already skipped or successful, you need no dispatch; if it shows
   `expected` with no run, dispatch it (step 2 below).
2. **Strict up-to-date means every advance of `main` invalidates your branch.**
   You must update-branch again, which pushes a new head, which re-runs check 1
   and re-invalidates check 2 (`review-admission.yml`'s `pull_request_target`
   job "Reset same-head admission immediately" exists precisely to do that on
   `synchronize`).
3. **`main` advances continuously and the runner queue is deep.** Measured
   2026-09-06: `main` advanced roughly every 5-10 minutes, 75 jobs were queued
   across 9 branches, and one PR's required gate sat `queued` for 17+ minutes.

So the window in which your branch is simultaneously up-to-date and has both
checks green is often shorter than the time it takes to earn them.

## What does not get you out of it

- **Auto-merge is disabled repo-wide.** You cannot queue the merge and walk away.
- **`--admin` does not bypass a *ruleset*.** Branch-protection admin override and
  ruleset enforcement are different systems. `gh pr merge <n> --merge --admin`
  against a ruleset-protected `main` returns, measured 2026-09-06:

  ```
  Required status check "SPipe Self Review Admission" is expected.
  ```

  That is also why the emergency procedure in `.claude/skills/spipe.md` adds a
  `bypass_actors` entry to the ruleset *before* `--admin`: the flag alone does
  nothing here. That procedure is user-authorized only.

## The loop that works

Ordering is mechanical, not stylistic — dispatching before update-branch wastes
the dispatch, because the update-branch push resets the admission.

1. **Update branch** to the current `main` (`gh pr update-branch <n>`, or rebuild
   your commit on `origin/main` per the scope rule in `.claude/rules/vcs.md`).
2. **Dispatch admission — only if `gh pr checks` shows it `expected` with no
   run.** If an `edited`/`synchronize` event already produced a skipped
   check-run, skip this step. Otherwise dispatch, only after step 1 has landed a new head, and only
   with the user's explicit instruction, since `self_attestation` is a claim in
   the repo owner's name:

   ```bash
   gh workflow run review-admission.yml --ref main \
     -f pull_request_number=<n> -f session_id=<session-label> \
     -f reviewer_model=<model> -f reviewer_effort=high -f self_attestation=PASS:0:0
   ```

   The dispatching actor must be the PR author.
3. **Poll BOTH checks**, not just the one you dispatched. `gh pr checks <n>` /
   `gh pr view <n> --json mergeStateStatus`. A green admission with a still-queued
   ratchet gate is not mergeable, and vice versa.
4. **Merge the instant both are green.** The published admission decision is
   short-lived — `doc/07_guide/infra/software_release.md` § Protected PR scoped
   self-review admission describes it as a ten-minute check that any push,
   retarget, ruleset change, diff drift, or expiry invalidates. Do not batch this
   step behind other work.
5. **On "base advanced", go back to step 1.** This is the expected outcome, not
   an error to investigate. Budget several full cycles.

## Notes

- Run the loop detached from anything slow. Every minute spent between step 3
  going green and step 4 is a minute in which `main` can move.
- `publish` is not a required check and fails on every PR; `UNSTABLE` is
  mergeable. See `.claude/rules/vcs.md`.
- A red job that is red for everyone is not yours. Diff your PR's failing job
  names against a recently merged PR before investigating.
