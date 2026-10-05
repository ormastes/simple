# Windows worker access violation reported as an impossible POSIX signal

The frozen 9d484 Phase 3 run completed 1,138 HIR modules, then its worker
returned -1073741819 (Windows 0xC0000005). The parent classified every value
below -128 as `-(128 + signal)`, printing signal 1073741691 and suggesting a
kill. This diagnostic was incorrect; the preserved worker status is an access
violation. The parent subsequently exited 139. No compiler binary was produced.

The repair recognizes known Windows statuses after the existing signed-status
normalization and restricts POSIX decoding to signals 1 through 127. Unknown
statuses retain the existing numeric fallback. It does not change process exit
codes, retry behavior, resource policy, or the underlying crash.

Five Simple regression scenarios exercise the observed access violation,
other Windows statuses, POSIX signals, sentinels, and boundary values. Native
execution is UNRUN until a repaired producer is available. This is a diagnostic
repair, not a claimed fix for the post-HIR memory failure.
