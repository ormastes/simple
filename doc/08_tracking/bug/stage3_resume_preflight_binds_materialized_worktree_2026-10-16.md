# Stage3 resume preflight evidence binds the materialized worktree state

Date: 2026-10-16
Lane: release_phase3 full bootstrap, Windows, worktree simple-phase3-s3.

## Symptom

`--resume-stage3-from-admitted` fails at stage2-verify with
`admitted Stage 3 resume lacks current authoritative preflight evidence`
even when HEAD, the admitted parent, and the planner receipt are all
current. `check-bootstrap-preflight.shs --verify-receipt` recomputes three
live bindings and compares them to the receipt captured at the admitting
lane's start:

- git_head (repo HEAD)
- source_snapshot_sha256 (tracked-content snapshot walk)
- git_state_sha256 (`git diff --binary --full-index HEAD` + untracked list)

The git_state binding includes the MATERIALIZED typechange set
(materialize-symlinks-windows replaces tracked symlinks with real content,
so `git diff` shows mode/content changes for those paths). The recorded
hash depends on the exact worktree state at the admitting lane's preflight.

## What invalidates it

Any later materializer round-trip (another bootstrap startup WITHOUT the
lane's materialization receipt exports undo+redo of the tracked links; a
killed lane mid-materialization leaves a partial set; CRLF or placeholder
restoration changes blob hashes) shifts the diff and the receipt never
verifies again. Killing bootstrap runs and retrying stage3 from the same
output therefore always lands on this failure.

## Required flow

1. One uninterrupted stage2 lane produces the admission, the planner
   receipt, the preflight receipt, and the materialization receipt.
2. Stage3 resume must start IMMEDIATELY, with
   `SIMPLE_WINDOWS_MATERIALIZED_LINKS_RECEIPT=<that lane's
   materialized-links/windows-materialized-links.*.env>` exported so
   bootstrap-materialized-startup validates instead of undo+redo
   (bootstrap-materialized-startup.shs skips the mutation when a valid
   receipt is supplied).
3. No git commits or tree mutations between the lane's preflight and the
   stage3 verify.

Operational corollary: never kill a bootstrap lane you intend to resume
from; the output's evidence chain is only self-consistent for the state
its own run captured.
