# smux window lifecycle

Source: `test/03_system/tools/smux_window_lifecycle_spec.spl`.
Status: NOT_RUN. Nine authored scenarios; zero executed. This authored mirror
does not claim generated-doc freshness or native coverage.

The shared `window_lifecycle_setup` creates an actual session and two windows.
`window_lifecycle_check` asserts the exact survivor, absence of target panes,
and removal of its closing marker; neither helper is a placeholder.

| Scenario | Steps and decisive oracle |
| --- | --- |
| Inactive deletion | Delete the inactive window through the API; active ID, attachment, notice, metrics remain and next window is id6. |
| Active deletion | Remove an active middle window; first registry survivor becomes active and third window retains its ID. |
| Final window | Remove both windows; target session/attachment/notice disappear, another session/client remain, repeated kill refuses. |
| Invalid targets | Reject cross-session, absent-window, missing argument and extra argument requests; counts unchanged. |
| Pure ownership gate | Actual transform refuses target PID and fd=0, preserves unrelated child authority, layout/output/client/ID counter. No native-close proof is claimed. |
| Split checkpoints | Remove one split window; its rollback refuses while the surviving window's real checkpoint still restores. |
| Managed two-client protocol | Reject stale lease and cross-session command; actual leased deletion preserves both leases; stale frame/input has exact missing-window error; replacement frame validates; final removal invalidates leases and reports missing session. |
| Real Windows PTY children | Compute 5859 in target cmd child; detach; checked kill; sibling computes fresh 3032; checked final cleanup and provider pending count zero. |
| Real Windows piped child | Actual cmd child computes 4336; checked final-window kill removes the session. |

Native kill retries are bounded by 200 attempts and a five-second monotonic
deadline checked between calls. This does not interrupt a native close call;
the Windows pipe owner may wait 5.1 seconds per child. Use an external 120-second
per-case process-tree watchdog. Output polling has at most 200 reads with 25ms
sleeps. Child-computed expected values do not occur in submitted command text.
Both native rows collect acquisition/exercise outcomes and attempt checked
cleanup of every retained session owner before assertions. Cleanup failure
remains a failing Result with authority retained; reset is never its oracle.

Pending/failing native cleanup and actual independent client-console recovery
remain unexecuted acceptance gates. Do not count protocol state or pure refusal
tests as those passes. The companion plan identifies their required receipts.
