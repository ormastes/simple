# macOS watchdog host-wide ps exceeds observation deadline

Status: sampler fix implemented; bootstrap revalidation pending. Date: 2026-09-22.
Owner: `scripts/resource/process-tree-rss-watchdog.pl`.

The third admitted bootstrap attempt (`build/evidence/macos-enforced-bd544/stage2-cocoa-retry`)
ended with exit 89 (`ps timed out`) despite a 5,000 ms observation budget.
Prior successful samples reached approximately 3,988 ms, sample gaps 3,991 ms,
and peak workload RSS 2,499,008 KiB. Its final receipt reported quiescent cleanup.
The 100 ms sampling target could not be met by repeatedly launching host-wide
RSS collection and a second executable for session inspection under host load.

The Darwin backend now uses one persistent, compiled/pinned native observer.
A bounded sysctl metadata snapshot drives the supervisor's existing membership
selection; libproc RSS and authoritative getsid calls touch only selected live
members. Birth identities contain seconds and microseconds and are checked
around memory collection. The portable Linux ps implementation remains intact.
No deadlines or memory limits were increased. This remains sampled containment,
with the documented unobserved escape/fork limitation, not a kernel memory cap.

Checks completed on macOS arm64:

- `process_tree_rss_watchdog_test.shs`: cap, escape/fork/orphan cleanup, stdin.
- `process_tree_rss_identity_test.pl`: PID/PGID reuse and unreaped root identity.
- `bootstrap_session_guard_test.shs`: installed identity, nested session admission,
  session helper replacement, and observed SID escape.
- `process_tree_rss_deadline_test.shs`: cadence, timeout/grace, bounded cold admission.
- `process_tree_rss_observation_budget_test.shs`: slow valid responses, hung
  observer, startup gate, and persistent live observation failure.
- `macos_process_observer_test.shs`: no ps dependency, persistent observer,
  hash pinning, helper cleanup, wrong birth identity, replacement, early close,
  malformed and oversized protocol.
- `process_observer_protocol_test.pl`: deterministic pre-admission EPIPE and
  bounded line read. Native C compiles with `-Wall -Wextra -Werror`.

Review identified a pre-admission SIGPIPE hole; the supervisor now installs its
ignore disposition before the first observer write and restores the inherited
disposition in the workload. Failure remains exit 89 with a receipt.

Three interleaved native compile measurements (seconds, 3,500 functions):

| Mode | Run 1 | Run 2 | Run 3 | Median |
| --- | --- | --- | --- | --- |
| Plain | 8.831714 | 8.835996 | 9.660636 | 8.835996 |
| Guarded | 9.909596 | 10.281471 | 10.613628 | 10.281471 |

Invocation overhead remains material: +16.36%, including helper compilation and
admission. Final receipt: 96 samples, peak 308,208 KiB, max duration 18.984 ms,
max gap 113.410 ms, no overruns, no observer errors/restarts. Local evidence is
under `build/evidence/macos-observer-native-20260922`; the measurement was taken
during final protocol hardening and is not a release benchmark. Linux runtime
behavior was not exercised on this Darwin host. No bootstrap was rerun because
the parent task exhausted its three-cycle limit.

## Native observer integration follow-up: unresolved detail EOF

A separately authorized attempt at `90fe7dc50e1` subsequently failed before
compiler work: `build/evidence/macos-enforced-bd544/stage2-native-sampler`.
The observer closed its output during a detail request. Its receipt records
exit 89, 38 completed samples, peak 43,936 KiB, maximum sample 42.997 ms,
maximum gap 120.531 ms, one observer error/restart for cleanup, quiescent=1
and no session escapes. The old native helper did not identify the syscall
or identity comparison that failed. **The cause of this EOF remains OPEN.**

A diagnostic-only follow-up records the operation, PID, return size and errno
for syscall/short-read failures, expected/actual birth identity for identity
mismatches, and the requested PID/identity in the supervisor's EOF message.
It does not suppress errors, extend budgets, or change exit/containment policy.

Deterministic `macos_process_observer_detail_test.shs` coverage injects failures
at both BSD identity reads, task RSS, and session reads; short reads; both
identity mismatches; ESRCH exit transitions at each syscall; a zombie; and a
successful live sample. The unchanged production detail function is compiled
into the fixture with syscall replacements. Its `-Wall -Wextra -Werror` build
and checks pass. A real unreaped-zombie probe returns 0/ESRCH for both BSD and
TASKINFO on this host, confirming that ordinary zombie exit is already handled.
Three bounded local workloads (500 sequential exits, 200 pipeline/fork groups,
40 xcrun/sw_vers/git discovery loops with pinned Clang 23) completed without
reproducing the integration failure. Logs and receipts are retained under
`build/evidence/macos-observer-exit-race-20260922`.

The diagnostic work ran no bootstrap. Another independently authorized native
attempt must capture the failing operation before any behavioral fix is claimed.
Invocation overhead remains OPEN as documented above.

## Attributed denial and retained-group cleanup

The next independently authorized attempt, `stage2-serialized-20260922`,
identified the operation: `bsd-before pid=98646 bytes=0 errno=1` (EPERM),
repeated after the observer restarted. Requested birth identity was
`1790077276:422699`. Exit 89 recorded peak 5,392,656 KiB below the 5,859,375
KiB sampled cap, but quiescent=0. Root/time PGID 92425 was killed; retained
bootstrap PGID 92426 survived reparented to PID 1 with further descendants.
The bootstrap owner manually validated and terminated that exact group and
confirmed removal. Thus this failure was neither a deadline nor an RSS breach.

Two fixes preserve fail-closed policy:

- Permission-denied detail reads receive independent `KERN_PROC_PID` proof.
  Only a successful empty PID result or the exact expected PID/birth identity
  in zombie state becomes `gone`. Live, reused, incomplete, or denied metadata
  remains an error. The original attempt did not record this proof, so its
  PID's actual live/zombie state remains unknown; no blanket EPERM exemption
  or successful bootstrap claim is made.
- Darwin cleanup requests fresh metadata without RSS/session detail calls.
  It can STOP retained groups and descendants using current birth identities,
  rediscover children while frozen, and KILL them even when detail permission
  remains denied. Metadata failure still cannot justify stale PID/group signals;
  that exceptional root-only fallback reports quiescent=0.

Evidence is under `build/evidence/macos-observer-denial-cleanup-20260922`.
The injected detail matrix checks denial at each syscall against live, gone,
zombie, reused, wrong-PID, short and denied kernel metadata. A real child
live/zombie/reaped lifecycle checks the actual sysctl proof under injected
libproc denial, including rejection of a mismatched birth identity. A real
macOS sandbox `process-info-pidinfo` denial demonstrates that actual EPERM for
a live process is still rejected. Tests compile with `-Wall -Wextra -Werror`.
The cleanup fixture creates a real separate child group and grandchild, denies
detail persistently, kills the direct root, and requires exit 89 with
quiescent=1 and no live survivors. PID/group reuse and metadata failure remain
covered by the identity regression. No bootstrap was run for these fixes.
Invocation overhead and source-matched bootstrap qualification remain OPEN.

## Live denied process: ownership attribution pending

The independently authorized `stage2-reviewed-531ac33` attempt proves the next
denial was live: PID 8004, state 2 (SRUN), expected/actual birth
`1790077981:225476`, successful 648-byte kernel proof, and BSDINFO EPERM.
Seed refresh completed in 44.32 seconds; failure occurred during Rust compiler
backfill. The receipt reports peak 3,030,288 KiB, maximum sample 34.817 ms,
zero overruns, exit 89 and quiescent=1. The prior retained-group cleanup fix
worked; no manual kill was needed. PID 8004's command and ancestry were not
recorded, and it was absent by the diagnostic follow-up.

A provenance-only change adds target kernel command, PPID/PGID/SID, effective
and real UID to denied-query diagnostics. Supervisor EOF evidence includes
root/expected session, retained versus current group leader identity, and the
selected metadata snapshot's ancestry bounded to 32 rows with cycle detection.
The command name is bounded and whitespace/control sanitized. None of these
fields changes process selection or permits ignoring live denial.

Tests cover exact command/identity attribution, control-character sanitation,
group-anchor evidence, ancestry order, cycle termination and the depth bound.
Evidence: `build/evidence/macos-observer-live-denial-20260922`.

The backfill log also records `rust-objcopy` PID 7959 aborting because its
`@rpath/libLLVM.dylib` dependency could not load. One guarded minimal objcopy
invocation reproduced that independent toolchain fault, but completed 42
samples/quiescent cleanup without EPERM. No causal link between this crash and
PID 8004 is established. A separate agent owns that toolchain fix/reproduction.
This watchdog follow-up ran no Cargo/backfill or bootstrap. Ownership of the
denied process, bootstrap qualification, and invocation overhead remain OPEN.
