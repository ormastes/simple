# Phase 1 verification false-pass audit

Base: origin/main e0dd873da1b7828389db4eb60e82972cc8245313.
Scope: the reachable Stage 1 path in `scripts/bootstrap/bootstrap-phase-verification.shs`, its authority owner, canonical controller units, and Phase 1 guide.

## Reproduced defect

Severity: P1. A phase-produced tool can rewrite the shared summary during a build/help probe. Removing its `UNSUPPORTED` rows makes the final `grep` report zero failures even though Phase 1 did not execute the required source checks/tests. The old verifier relied entirely on that file and returned success.

The canonical unit's `mask` fixture reproduces this with real shell/file operations and an otherwise valid current-generation fixture. Before the change, the unit exited 1 with `mask summary admitted unsupported Phase1`: the verifier had returned 0. The retained local red log is `build/review/phase1-mask-before.log` (execution session 9778).

An initial read-only-file hypothesis was rejected: canonical `sh` already terminates when the special builtin that truncates the summary fails. That existing behavior is preserved as a regression case and is not represented as a newly fixed false-pass. Ordinary later summary appends were unchecked and now explicitly fail closed.

## Change

The verifier retains the number of unsupported tasks in memory and includes both that count and its existing failure latch in the final decision. This state is independent of the fail-fast scheduler, so supported tasks still produce their evidence. The summary now includes `unsupported_tasks`.

Summary initialization, headers, terminal task rows, and final result writes are checked. Summary read errors also refuse acceptance. Removing failure rows or encountering a late write error cannot turn an already incomplete matrix into a successful process exit.

The executable unit `test/01_unit/scripts/bootstrap_phase_stage1_native_build_authority_test.shs` now covers summary masking, masking followed by a read-only append fault, and a stale read-only initial summary. Its existing admitted producer routing, server build/help, and stale-artifact removal assertions remain. Read-only cases explicitly report when host privilege/filesystem semantics cannot enforce that fault; the ordinary masking case is independent of file permissions. `--summary-only` runs the focused new scenarios without repeating the existing producer cases.

## Requirement audit

| Concern | Reachable Phase 1 behavior and evidence |
| --- | --- |
| Discovery/filter failures and empty inventory | Source-test discovery is not entered for Stage 1. Required source rows are `UNSUPPORTED`, so Stage 1 is incomplete. No test-inventory coverage is claimed. |
| Interpreter and compile modes | Neither source-test mode is admitted for the bootstrap seed in this verifier. Later CLI/test-runner phases own them. No new Stage 1 runner was invented. |
| Malformed or duplicate test JSON | Stage 1 has no source-test JSON parser on its reachable path; this is a later-phase gate. |
| Executed=0, skipped or pending tests | No Stage 1 source test is claimed executed. Unsupported tasks must continue to prohibit overall PASS. |
| Command/pipeline status | Build/help commands execute through the timeout owner with direct exit-status capture. Every nonzero status refuses its task. Recognized crash/timeout codes get their labels; other signal-derived codes remain failures. |
| Stale or missing compiler authority | The current-generation unit covers PATH/unregistered tools, modified producer/snapshot/marker, pending publication, and modified produced tool. It passed during this audit. |
| Tool containment | The containment unit covers canonical registration and traversal/alias refusal. It passed during this audit. |
| Missing or stale build output | Existing canonical producer unit removes old outputs and rejects exit-zero producers that emit no executable; unsupported full-matrix status remains required. |
| Summary masking/write failure | Reproduced false-pass; fixed with the in-memory verdict and checked evidence I/O. |

The canonical units use controlled fake producers to test the controller; they do not constitute a successful real bootstrap or source-test run. This change leaves the intentionally unsupported Phase 1 source-test contract intact. Independent review and current CI remain required before publication/admission.

## Verification evidence

All commands ran in the isolated `D:/wk-phase1-falsepass-astra` worktree through `C:/msys64/usr/bin/bash.exe -lc`. The baseline focused unit used `--summary-only`; the fixed run executed the full canonical producer unit, including its existing cases. No already-green unit was repeated. The initial rejected hypothesis, authentic baseline reproduction, and final green consumed the three-cycle limit.

| Check | Result | Retained local evidence |
| --- | --- | --- |
| Unmodified baseline verifier, extended canonical unit | FAIL, verifier falsely returned 0 after masking | `build/review/phase1-mask-before.log`, session 9778 |
| Fixed verifier, full canonical producer/summary unit | PASS, exit 0 | `build/review/phase1-summary-after.log`, session 76824 |
| Current authority unit | PASS, exit 0 | `build/review/phase1-current-authority.log`, session 38840 |
| Tool containment unit | PASS, exit 0 | `build/review/phase1-tool-containment.log`, session 3144 |
| Shell syntax, whitespace, working direct-environment and numbered-artifact guards | PASS | session 68997 |

SHA256 of the fixed verifier: `03a0fbabd1bcbf1385ff47afedb7429e11b084db9a42d88ad8f56785c2ba2733`.
SHA256 of the identical test bytes used for red and green: `9dbb0f2fb14cfce2388bad0957de8770de38714bbfb5a7ad46be479bdf1c52e5`. After green, only the initial-read-only case's explanatory comment was corrected to describe its already-existing refusal accurately.
SHA256 of the red log: `1a7c0303ac7e56dd4a921bde07682ff2de1b67f17fe33e879c9db6c64b1c6b0a`.
SHA256 of the green log: `c1e2b3a868c5f14a83f191b945f83773d78568747f9c45726df7ad78d07021e2`.

The change adds constant-size shell state and no new subprocess or unbounded storage on the verification path. No wall-time or RSS improvement is claimed. Self-review found no remaining P0/P1 issue in this scoped Phase 1 path; independent review remains the publication gate.
