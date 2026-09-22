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
