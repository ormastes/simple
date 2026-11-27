# phase-ladder-resume reuses a stale phase artifact built from different source

- Status: verification-pending
- Date: 2026-11-27
- Component: `scripts/bootstrap/phase-ladder-resume.shs`, `.github/workflows/phase-ladder-rung.yml`

## Symptom

Run 45799158689 reused a phase-1 compiler from run 45350485434 (Nov 24) against
current source. That compiler failed with parser errors, because the resume step
picked the newest unexpired `ladder-<platform>-r<rung>` artifact on the branch
without checking which source revision built it.

## Root cause

`phase-ladder-resume.shs` filtered artifacts on name, expiry and branch only.
The producing run's `head_sha` was never consulted.

## Fix

Each candidate run is gated by `revision_reusable` before download (and before
the four-candidate limit, so stale artifacts cannot crowd out a usable one). The
revision is the producing run's `head_sha` (`gh api repos/<repo>/actions/runs/<id>`).
Reuse requires `head_sha == $GITHUB_SHA`, or `compare` status `ahead`/`identical`
with no changed file under `src/compiler/`, `src/compiler_rust/`, `src/runtime/`,
`src/lib/`, `src/app/cli/`, `config/bootstrap.sdn`, `scripts/bootstrap/`
(except `scripts/bootstrap/tests/`). Fail closed: unknown sha, unknown target,
compare failure, diverged/behind, or a change list at GitHub's 300-file cap all
mean "rebuild fresh" (a clean cold start, not a discovery error).

## Tests

`scripts/bootstrap/tests/phase-ladder-resume-revision-test.shs` (11 fixtures with a
fake `gh`: stale, matching, docs-only ancestor, newest-stale/older-match, lib
change, unknown revision, compare error, diverged, behind, truncated list, empty
target). Advisory row `push-phase-ladder-resume-revision` in
`config/check/must_check_gates.sdn`.

## Verification pending

Fixture-proven only; needs a real phase-ladder run on this branch to show a stale
artifact rejected and a current one reused.
