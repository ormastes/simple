# Browser Static Shell Cache Spec Timeout

## Closed 2026-09-13 — No longer times out; the three scenarios complete and pass

- **measured** (Rust seed `bin/simple` v1.0.0-rc.1, Windows): `bin/simple run test/01_unit/app/ui/browser_static_shell_cache_spec.spl` finished in **180 s**, exit 0 — `3 examples, 0 failures`, `declared>=3 executed=3 passed=3 failed=0`, outcome=OK. The reported failure was a timeout at both 120 s and 300 s; it now completes inside the 300 s bound.
- **inferred**: the spec is still slow (3 minutes for 3 scenarios), so the Next Step's profiling suggestion — attributing cost to `render_frame` vs `render_cached_static_frame` vs `pixels_rgba_i64` — remains worth doing as perf work. That is not this bug, which was filed as a timeout.
- Caveat: measured via `bin/simple run`, not `bin/simple test --mode=interpreter` as originally reported; the runner is non-functional on this Windows host (`process_run_bounded` kills every child immediately), so runner overhead is not included in the 180 s.

Date: 2026-06-14
Status: CLOSED 2026-09-13 (no longer times out; 3/3 pass in 180s)

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
