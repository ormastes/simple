# Sharded claim-and-show deletes its own display input

- **Status:** FIXED (2026-11-27)
- **Priority:** P1 (source repair landed in `6bc1e955a0b` and `0bf93c3738c`; live-verified on `release/1.0.0`).

## Failure

On release/1.0.0 at `6d496f82c5acabc2fc52b2b78146272e664dc371`,
`bug-claim.shs show <id> --intent for_fixing --session <owner>` successfully
publishes the claim shard and prints `CLAIMED`, then exits 2. Its display
commands report `awk: fatal: cannot open file /tmp/...` and status can print
`state=none status=` even though an independent status command confirms the
live persisted claim. Treating the nonzero exit as an unclaimed bug can cause
incorrect retries and ownership reporting during a parallel repair campaign.

`cmd_show` called `cmd_claim` in a subshell. Acquiring the claim lock installs
an EXIT cleanup that removes the shared `MERGED_DB` pathname. The child's
successful exit therefore removes the parent's display input. The legacy
single-file fixture did not exercise this temporary-view ownership boundary.

## Repair

Call `cmd_claim` in the current shell. Claim publication, display, and cleanup
now use the same database variables and lifetime. The lock remains held while
the bounded display reads the committed view, then the existing owner-token
cleanup releases it and removes temporary files. Refusal and closed/unknown
bug exit codes retain their existing paths. No database schema, sealing,
ownership arbitration, or unrelated bug status changes are needed.

## Executed evidence

Regression: `sh scripts/check/check-bug-claim-sharded-show.shs`.
The fixture uses the real public CLI, real legacy and per-bug shard files,
and real CRC32 sidecars under the existing fixture-only algorithm override.
It does not replace the claim, lock, merge, or sealing implementations.

- Original implementation: regression exit 1 because `show ACTIVE` returned
  2 after independently confirmed persisted ownership; the display reported
  deleted temporary input files.
- Repaired implementation: regression exit 0 with
  `PASS: sharded claim-and-show, both tables, details, refresh, refusal, read-only, release and cleanup`.
- Existing single-file protocol regression: `BUG_CLAIM_DB=<nonexistent private
  path> sh scripts/check/bug-claim.shs --selftest` exited 0 and printed
  `bug-claim selftest PASS`. The private path keeps the fixture independent
  of the real sharded database. This includes non-sharded claim-and-show,
  lock ownership, invalid arguments, and workflow transitions.
- Both `bugs_active` and `bugs` rows create real claim shards and display
  current main rows, descriptions, and owner state. Difficulty and environment
  details remain visible.
- Same-owner refresh succeeds. A rival receives exit 3 without changing the
  original shard. Read-only display leaves the shard byte-identical. Release
  restores `open`. Every operation leaves the frozen legacy file unchanged,
  no merged/work temporary files, and no claim lock.

Windows Git sh ran these shell-owner checks in the isolated worktree
`C:/dev/wt/g100-gui_evidence`. Logs are retained in its
`build/bug-claim-show/red.log`, `green.log`, and `legacy-selftest.log`.
Shell syntax and working/staged direct env/process guards also passed.
This evidence does not claim
Simple compiler, native runtime, GUI, or bootstrap qualification.

## Live Verification on `release/1.0.0` (2026-11-27, lane `w3-2-scripts-specs-hygiene`)

- **Landed fix commits (ancestors of base `74713fbd005`):**
  - `6bc1e955a0b` (`fix(tracking): preserve sharded view through claim display`)
  - `0bf93c3738c` (`fix(tracking): define die before sharded DB init and avoid awk -v newlines in bug-db-shard`)
- **Live regression re-run (Windows Git sh in `C:\dev\wt\w3-2-scripts-specs-hygiene`):**
  - `sh scripts/check/check-bug-claim-sharded-show.shs` -> exit `0`
  - Verbatim output: `PASS: sharded claim-and-show, both tables, details, refresh, refusal, read-only, release and cleanup`
- **Tracking closure:** Updated `doc/08_tracking/bug/db/bug_claim_sharded_show_deletes_parent_merged_view_2026_11_10.sdn` (`status` -> `fixed`, `valid` -> `true`) and appended a `done` row to `bug_fix_claims` closing the stale `fixing` claim (`01a1c3cc/gui_evidence`).
