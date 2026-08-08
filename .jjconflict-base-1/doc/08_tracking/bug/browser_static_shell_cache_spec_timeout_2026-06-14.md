# Browser Static Shell Cache Spec Timeout

Date: 2026-06-14
Status: open

## Symptom

`test/01_unit/app/ui/browser_static_shell_cache_spec.spl` times out as a whole
file under both the default 120 second runner timeout and an explicit
`--timeout 300` run.

## Evidence

- `./bin/simple test test/01_unit/app/ui/browser_static_shell_cache_spec.spl --mode=interpreter`
  failed with `Error: Test timed out after 120 seconds`.
- `./bin/simple test test/01_unit/app/ui/browser_static_shell_cache_spec.spl --mode=interpreter --timeout 300`
  failed with `Error: Test timed out after 300 seconds`.
- `./bin/simple test test/01_unit/app/ui/browser_static_shell_cache_spec.spl --list`
  lists three scenarios quickly, so discovery is not the issue.

## Impact

The static-shell cache suite is not currently usable as a fast guard for
BrowserBackend runtime queue diagnostics. The focused replacement guard
`test/01_unit/app/ui/browser_backend_runtime_queue_spec.spl` passes in roughly
1.3 seconds and covers the queue-provenance API path.

## Next Step

Split or instrument the three static-shell scenarios to identify whether the
timeout is in repeated `render_frame`, `render_cached_static_frame`, or
`pixels_rgba_i64` cache reuse.
