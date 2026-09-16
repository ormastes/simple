# Bug: `bin/simple test <file> --timeout N` still hard-caps at 120s (light daemon)

**Date:** 2026-07-02
**Component:** `src/app/test_runner_new/test_runner_client.spl`,
`src/app/test_daemon/light_daemon.spl`.

## Symptom

`bin/simple test some_spec.spl --timeout 900` still kills the test process
after exactly 120s (`[TIMEOUT: Process killed after 120s]`, `Duration:
120007ms`), even though `--timeout` is parsed correctly into
`ClientRun.timeout_secs` in `test_runner_client.spl::parse_client_run`.

## Root cause

`test_runner_client.spl::main()` is a thin client to a persistent "light
daemon" (`.build/test_daemon_light/`). It writes the request as **just the
file path** (`rt_file_write_text(req_path, run.path)` — no timeout value),
then polls for a response file for up to `run.timeout_secs`. The daemon side
that actually spawns/kills the child test process enforces its own fixed
120s budget, independent of the client's requested timeout — the timeout
value never crosses the request-file boundary.

## Impact

Any spec that legitimately needs more than 120s (e.g. a full 800x600
software-rasterizer session under the interpreter — see
`doc/08_tracking/bug/jit_game2d_backend_method_dispatch_sigsegv_2026-07-02.md`
for why the JIT path isn't usable here) gets silently truncated at 120s no
matter what `--timeout` is passed on the command line.

## Workaround

Pass `--no-session-daemon` to skip the light-daemon round trip entirely —
that path (`test_runner_single.spl` via `process_run_timeout(binary,
["test", "--no-session-daemon", path], run.timeout_secs * 1000)`) honors the
full requested timeout correctly:

```sh
bin/simple test --no-session-daemon path/to/slow_spec.spl --timeout 900
```

Used by `scripts/check/check-game2d-breakout.shs` for exactly this reason.

## Suggested fix (not attempted — shared test infra, out of scope for this lane)

Include the requested timeout in the request file payload
(`test_runner_client.spl`) and thread it through to whatever spawns/kills
the child process in `light_daemon.spl`, instead of a fixed 120s.
