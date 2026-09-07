# Feature: scilib-port-remaining

## Raw Request
$sp_dev complete scilib port remaining.md plan and push pr.

## Task Type
todo

## Refined Goal
Complete every feasible acceptance criterion in the SciLib remaining-port plan, preserve explicitly unavailable host evidence as active blocked work only where unavoidable, and submit the resulting reviewed change as a pull request.

## Acceptance Criteria
- AC-1: Every unchecked SciLib plan criterion is audited against implementation and executable evidence; each satisfied criterion is checked only with matching evidence, and every unsatisfied criterion has an actionable tracked blocker.
- AC-2: The LAPACK Layer B/C APIs use wrapper types rather than primitive public boundary parameters, and the LAPACK singular/error-path scenario is executable without weakening its assertion.
- AC-3: The BLAS norm-Inf path has a regression scenario whose maximum value occurs at a non-zero index and verifies the documented 1-based-to-0-based correction.
- AC-4: The remaining math-block, ML, ndarray, BLAS, LAPACK, CUDA/Fortran, dataframe, and perf-sugar plan rows have current-host evidence or an explicit active blocked record with prerequisite, resume command, retained artifact, owner, and reviewer.
- AC-5: Focused pure-Simple verification passes once for each changed acceptance scenario; no placeholder, skip, or assertion weakening is introduced.
- AC-6: Knowledge is updated in the SciLib plans, relevant developer guide, and SciLib feature/layer expert entries; unresolved gaps have file-and-line bug records.
- AC-7: The scoped change is committed on an isolated branch and a GitHub pull request is created without including unrelated dirty-worktree files.

## Scope Exclusions
- Unrelated dirty files and unowned active lanes.
- Native CUDA or external-host execution unavailable on this macOS host; those remain active blocked rows rather than completed work.

## Cooperative Review
N/A — the existing plan identifies one coherent, already-modified lane and its interface names/spec helpers are established; broad sidecar delegation is not authorized in this session.

## Phase
dev-done

## Log
- dev: Created state file with 7 acceptance criteria (type: todo).
- impl: Replaced the BLAS norm-Inf placeholder audit with a non-zero-index behavioral regression and refreshed the SciLib guide and expert handoff.
- push: Fixed `push-no-direct-rt` to compare the exact pushed ref against its committed outgoing-range base; focused selftests pass 19/19 and the SciLib tip is 6313 == 6313 base sites.
- push: Fixed the analogous interpreter-extern push ratchet after current main proved independently red; its 9-fixture selftest and exact SciLib tip/base scan pass with zero branch-added gaps.
- push: Converted the blocking SFFI v2 aggregate to an exact committed-base failure-set ratchet; five focused fixtures distinguish unchanged red mainline debt from a newly failing topic guard.
- push: Reproduced the main-test-runnable clean-fixture parse failure on the current debug seed and restored positional construction for the reserved `auto` field; reopened the prematurely closed portability bug.
