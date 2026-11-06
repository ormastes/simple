# Session retirement returned success without confirmed leader retirement

Status: source repair; focused native fault fixture PASS on macOS arm64 (cycle 1).
Owner: canonical OS session FFI boundary `runtime_process_tree.c`, shared by
native archives and the Rust runtime. No application-local runtime calls.

The reap loop previously exited its two-second budget with `leader_gone` false
and still returned 0 after the second signal sweep. Non-EINTR/ECHILD wait errors
also reached that success. The enumeration loop ignored signal denial and other
signal errors, so 0 did not even establish its documented signalled-members
contract. These are source-confirmed causes, not an executed reproducer claim.

The owner now returns `-ETIMEDOUT` when reap is unconfirmed, propagates wait and
signal errors, bounds repeated EINTR by the same deadline, and refuses clock
failure. ESRCH after enumeration remains a benign exit race. A failed signal
still permits attempts on remaining session members. Ordinary failure retains
Simple facade ownership. Post-reap second-sweep failure still returns the
existing dedicated sentinel; the facade returns Err and discards raw PID
signal authority because that PID may be reused. No blind post-reap retry.

Success retains the existing header scope: session enumeration, signal delivery
and leader reaped/no longer waitable. It does NOT certify immediate descendant
retirement, nor contain descendants that create a new session. No app spawn
migration or stronger `all_stopped` claim is included in this repair.

`src/runtime/test/process_tree_retirement_fault_selfcheck.c` includes the actual
owner with fixture-only syscall interception. It exercises real session spawn,
a TERM-ignoring helper, timeout preservation and confirmed reap; injected signal
denial, wait deadline/error/repeated EINTR, post-reap enumeration allocation
failure and clock failure. A parent alarm and independent child alarms bound
execution. The existing `process_tree_selfcheck.c` is the adjacent owner gate.
The existing adjacent selfcheck remains NOT_RUN; it was excluded because its
legacy 300-second helpers lack the new fixture's independent child watchdog.

The correction is OS/FFI boundary code under explicit authorization. The
pure-Simple facade preserves the owner/error distinction; it is not an
independent pure-Simple OS implementation. No dual-run shadow PASS or full
cross-platform runtime qualification is claimed.

## Focused native evidence — 2026-11-07

One authorized compile/run on macOS 26.5 arm64 with Apple clang 17.0.0
(clang-1700.6.4.2): compile exit 0, run exit 0, 40 assertions passed / 0 failed.
The actual TERM-ignoring control and six injected failure cases executed.
Compile elapsed 0.316s; run elapsed 4.725s. External budgets 30s/35s and internal
parent/helper alarms 30s/12s. Source SHA256 values matched before/after.

Artifact SHA256: `8e186c1f14c1d02e3df891c393511c9f621dcdcc90432baa2fffd7645b5bc65e`.
Session evidence: `/private/tmp/ptree-retirement-20261107.receipt.sdn`, with
`.build.log`/`.run.log` at the same prefix. No repeated native run. Linux,
FreeBSD, Windows unsupported-arm execution, Simple facade runtime and whole
compiler/HIRworker integration remain NOT_RUN. No whole-tree-empty proof.

Compile command (30-second external timeout):
`/usr/bin/cc -Wall -Wextra -Werror -I src/runtime -o /private/tmp/ptree-retirement-20261107 src/runtime/test/process_tree_retirement_fault_selfcheck.c`
from the isolated owner worktree. Run command (35-second external timeout):
`/private/tmp/ptree-retirement-20261107`.
The fixture's original authoring-stage NOT_RUN header is retained unchanged so
its tested source hash remains exact; this dated receipt supersedes that status.
App HIR worker spawn migration and full lifecycle integration remain OPEN.
