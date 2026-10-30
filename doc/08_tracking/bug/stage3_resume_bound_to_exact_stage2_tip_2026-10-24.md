# Stage 3 resume is bound to the exact clean tip the admitted Stage 2 was built from

Date: 2026-10-24. Lane: windows-gnu (x86_64-pc-windows-gnu), `--stop-after-stage2 --produce-stage3-receipt`
followed by `--resume-stage3-from-admitted=<out> --bootstrap-receipt=<out>/stage3-planner-admission.receipt`.

## Symptom

An admitted Stage 2 (built at `e9ba4b4a7ea`, receipt produced) cannot be resumed at any other
tip, and not even at that tip when the resume script itself needs a fix:

1. Resume at `0f943d1328d` (contains #4347, the resume-vector fix) passes the
   `build_args_sha256` admission check, then fails:
   `stage2-sanity-error: frontend-status role=p2_add failure=bounded-helper-sha` and
   `sanity-receipt role=bootstrap0 failure=status-verification`.
   The sanity receipts record `helper_sha256=79a3fc4d...` of
   `scripts/bootstrap/run-process-group-bounded-log-windows.py`; a later scripts-only PR changed
   that file. Restoring the single file from `e9ba4b4a7ea` makes the hash match.
2. Next gate: `FAIL - authoritative preflight receipt rejected: .../bootstrap-preflight.env` and
   `bootstrap-policy-error: admitted Stage 3 resume lacks current authoritative preflight evidence`
   (exit 64). `bootstrap-preflight.env` records `git_head=e9ba4b4a7ea` plus source-snapshot and
   git-state hashes.
3. Pinning the worktree back to clean `e9ba4b4a7ea` and overlaying only
   `resume-stage3-from-admitted.sh` from `0f943d1328d` is rejected the same way (dirty tree).

## Why it is a bug

The resume path needs fixes (#4347 reconstructs the stage2 env vector with `OS=Windows_NT`) that can
only exist at a newer tip than the Stage 2 it must resume. Every scripts-only fix therefore forces a
full Stage 2 rebuild (about 25 min cold plus sanity) even though no compiler input changed.

## Proposal

- Allow re-sealing the preflight and sanity evidence at a new tip when only `scripts/**` changed
  relative to the recorded `git_head` (compiler/runtime/source inputs unchanged), recording both heads.
- Or exempt resume helper scripts (`resume-stage3-from-admitted.sh`,
  `run-process-group-bounded-log-windows.py`) from the helper-hash pin and the git_head/git-state binding.

Workarounds tried are tagged WA-HELPER-PIN-STAGE2 and WA-PIN-TIP-PLUS-4347 in
`build/bootstrap/logs/manual-link-notes.md` (local, uncommitted).
