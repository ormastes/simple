# Daemon publication regression evidence — 2026-11-07

STATUS: BLOCKED for landing. Source review is not runtime qualification.
Target: `release/1.0.0`; PR #7415. Production scope is the shared DaemonRunner
and its V1 spool writers, not every app-specific daemon loop.

The SSpec calls nine shared real-filesystem cases from
`test/fixtures/daemon_sdk/publication_regression.spl`. The standalone diagnostic
entrypoint also accepts a case name, allowing independent failure collection.
No successful assertion is substituted for an unavailable runtime.

## Diagnostic environment

Linux aarch64. Unadmitted pure-Simple producer SHA256:
`afae09d224390a57d675a128a052626c3aa665c032481928332ebdc2859d7350`.
Source base `662c9c4fe01b07f3712faeccab945ee69fcd889c` plus this PR's regression
and envelope guard changes. Final fixture SHA256:
`332845859957833a95d59e393ec8d7e8fc835134a23a14cd4491cac22300b68f`.
Final protocol SHA256:
`2860ae899a76cef1474680c9efe7c64ee18a3f63b11abf98d05e8b601e9dda50`.

Native command options: `native-build --backend llvm --runtime-bundle
core-c-bootstrap --source src --source test/fixtures --entry-closure --entry
test/fixtures/daemon_sdk/publication_regression.spl --threads 1 --mode one-binary`.
Private HIR/frontend/native caches and TMPDIR; `SIMPLE_NO_STUB_FALLBACK=1`;
360-second process-group build timeout, 30-second case timeout.
Final artifact SHA256:
`62b0b1cb21cf4136647b062c3f39629413af4ee7178b0688ac3411860a6d5b5a`.

## Actual final diagnostic results

| Selection | Exit | Observation |
| --- | --- | --- |
| publication | 0 | Failed publication retains original request and stops dispatch |
| identity | 0 | Mismatched response identity refuses publication |
| success | 1 | Assertion failure; earlier syscall trace locates inconsistent path hashes |
| missing-ack | 0 | Missing request blocks further dispatch |
| prefix | 1 | Assertion failure; not independently attributed |
| refusal | 0 | Nonempty replacement directory refuses acknowledgement |
| injection | 0 | Header/key injection rejected; handler effect retained once |
| outer-loop | 0 | Failure at cycle 100 skips periodic cleanup |
| error-status | 1 | Assertion failure; not independently attributed |

Logs: isolated worktree `build/daemon-publication-native/build-v3.log`,
`cases.txt`, `case-*.log`, `deletion.trace`, `final-source-artifact.sha256`.
The [hash disagreement report](../08_tracking/bug/native_daemon_spool_hash_disagreement_2026_11_07.md)
records exact syscall paths without assigning an unproven compiler root cause.

Admitted compiler is unavailable at `bin/release/aarch64-unknown-linux-gnu/simple`.
SSpec execution, generated manuals, core/lib/MCP/LSP checks and native smokes
remain NOT_RUN/BLOCKED. Six diagnostic successes do not satisfy those gates.
The handwritten manual is labelled authored, not generated runtime evidence.

Astra reviewed source and requested the ordinary-multiline field-value assertion;
it is included. No remaining P0/P1 was found in that source review. An exact
commit review follows; neither review authorizes merging over failing tests.

## Pre-guard sensitivity control

A separate worktree at `662c9c4fe01b07f3712faeccab945ee69fcd889c`
compiled the identical final fixture without the new envelope guard. Build exited
0; `program injection` exited 1. The retained bad-request file contains
`field.output=ok`, followed by `ordinary` and `  id=other`: the writer published
the injection instead of rejecting it. The patched diagnostic selection exits 0.
Thus the same test distinguishes the pre-guard defect from the guarded behavior.
This is diagnostic sensitivity evidence, not admitted qualification, and it does
not establish a pre-fix control for the original response-write ordering defect.

Control artifact SHA256:
`2b9e750433a83482032364b5b3dc2aa9e6a66fe2a938e007fa986fc6b948d8ed`.
Control logs: `/home/yoon/dev/simple-daemon-publication-before-20261107/build/daemon-publication-control/`
(`build.log`, `injection.log`, `injection.exit`). Both worktrees retain separate
caches, source snapshots and outputs. No production source was swapped during a build.
