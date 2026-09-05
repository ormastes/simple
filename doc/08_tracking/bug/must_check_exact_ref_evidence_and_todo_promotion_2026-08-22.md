# Must-check exact-ref evidence and TODO promotion

- Status: RESOLVED
- Owner: primary Codex must-check lane
- Date: 2026-08-22

## Failure

The bootstrap producer writes automated evidence below ignored `build/`, while
the push consumer hashes evidence from the live worktree instead of the exact
pushed revision. A committed ledger can therefore depend on local-only bytes.
In addition, registry rows declared `todo` have no bootstrap-owned transition
that can record their first real PASS, and any manually introduced PASS is
discarded when the source fingerprint changes.

## Required repair

- Retain production evidence in a committed repository path and validate its
  blob from the exact pushed revision.
- Refuse production bootstrap recording when fingerprinted inputs differ from
  `HEAD`.
- Add an explicit, fail-closed receipt import for TODO rows. Carry an imported
  PASS only while its committed evidence blob and hash remain valid.
- Preserve automated gate invalidation by source fingerprint.
- Add exact and adjacent regressions for missing/ref-divergent evidence and
  first-PASS/carry-forward behavior.

## Verification

The focused tiering fixture passed after proving first receipt promotion,
unchanged carry-forward, independence from modified/removed live-worktree
bytes, rejection when the pushed revision itself omits the evidence blob, and
bounded one/two-ref hook paths. Cycle 1 completed in 8.73 seconds; cycle 2 after
the Sdoctest/registry follow-up completed in 8.25 seconds.
