# Focused HIR warmup fallback ignored worker retirement

Status: source repair; policy tests and native lifecycle gates NOT_RUN.

`native_build_focused_capsule_shards_v1` previously used only `hir_run.code`.
Failed warming could fall back while `hir_run.all_stopped` was false, allowing
in-process work to overlap an unretired child. The coordinator now gives
retirement failure precedence even over code0, calls the existing environment
facade to restore the three saved values, and returns the existing `fail` sentinel before MIR or
in-process fallback. Successful retirement retains existing ready/fallback
behavior. As in the surrounding owner, restoration calls ignore their boolean
results and absent values were captured as empty strings; exact absence or
successful environment restoration is not claimed. The production outcome helper has four focused policy regressions.

This change neither kills nor reaps a worker. The existing plain-PID lifecycle
still has incompatible provider semantics: native SIGTERM-only versus Rust
kill-and-reap. Bounded TERM/grace/KILL/reap, descendant containment and retained
cleanup-failure ownership require a separate canonical process-owner migration.
No PID-liveness observation or source-policy test is native retirement proof.

Required native regression: deadline a TERM-ignoring helper and assert no
replacement/fallback before an exact owned retirement receipt; preserve timeout
as a failing row. Include cleanup/ack failure, descendant-held streams and a
provider which already reaps on kill. Use an independent bounded watchdog.
