# Bug: `bin/simple test` env passthrough to spec bodies is unreliable — root-caused, NOT fixed (architectural)

- **Date:** 2026-07-29
- **Status:** open — root cause confirmed deterministically, fix requires a
  session-daemon protocol change (out of scope for a minimal/additive patch)
- **Severity:** high (silently stale custom env vars inside `it` bodies;
  deterministic, not flaky, once you know the trigger condition)
- **Binary under test:** `bin/simple` (resolves to the Rust bootstrap seed,
  `src/compiler_rust/target/debug/simple` — printed
  `WARNING: this Rust-built Simple binary is a bootstrap seed only` on every
  invocation in this repo checkout; the env-routing code path involved
  (`test_runner_new`, `test_daemon`) is pure Simple and identical on the
  self-hosted binary, so the finding is not seed-specific, but re-verify on
  the self-hosted binary before treating counts as final).
- **Symptom as reported:** `env_get()` calls inside `it` bodies under
  `bin/simple test` "unreliably" see custom-exported env vars
  (`env_probe_spec.spl` example).

## 1. Reproduction (deterministic, 5/5 both directions)

Probe file `/tmp/env_probe_spec.spl`:

```
use std.spec.*
use std.io_runtime.{env_get}

describe "env probe":
    it "sees MY_PROBE_VAR from parent env":
        val v = env_get("MY_PROBE_VAR") ?? "MISSING"
        print "PROBE v=[{v}]"
        assert_equal(v, "hello")
```

Default invocation, run 5 times:

```
MY_PROBE_VAR=hello SIMPLE_EXECUTION_MODE=interpreter bin/simple test /tmp/env_probe_spec.spl
```

Result: **5/5 FAIL**, deterministically. Every run prints `PROBE v=[]`
(empty, not "MISSING" — see §4 note) and `Results: 1 total, 0 passed, 1 failed`.

Same probe with the session daemon explicitly disabled, run 3 times:

```
MY_PROBE_VAR=hello SIMPLE_EXECUTION_MODE=interpreter bin/simple test /tmp/env_probe_spec.spl --no-session-daemon --no-session-share
```

Result: **3/3 PASS**. Every run prints `PROBE v=[hello]` and
`Results: 1 total, 1 passed, 0 failed`.

This isolates the variable precisely: **whether the run goes through the
test-session daemon** is the entire difference. It is not flaky in the sense
of "sometimes passes, sometimes fails on the same command" — it is
deterministic *per daemon lifetime*: it fails 100% of the time a daemon
process is already alive and was started with a different/absent env, and
passes 100% of the time no daemon exists yet (first invocation spawns one
that inherits the current shell's env correctly). "Unreliable" in the
original report describes the experience across many invocations spanning
daemon restarts, not true nondeterminism within one daemon's lifetime.

## 2. Root cause, confirmed with file:line

1. **`bin/simple test <file>` defaults to session-daemon routing.**
   `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl:250-251` —
   `var session_share = true` / `var session_daemon = true`. No CLI flag is
   needed to opt in; `--no-session-daemon --no-session-share` are required to
   opt **out**.
2. **The runner routes through the daemon before any direct execution path.**
   `src/app/test_runner_new/test_runner_main.spl:218-236` — if
   `session_daemon or session_share`, calls
   `test_daemon_ensure_responsive(daemon_config)` and, on success, executes
   every file via `run_tests_via_daemon(...)`, returning before the direct
   `process_run_bounded`-based path (used by `--no-session-daemon`) is ever
   reached.
3. **Daemon reuse has zero env awareness.**
   `src/lib/nogc_sync_mut/daemon_sdk/client.spl:26-53`
   (`daemon_ensure_running` / `daemon_ensure_responsive`) decide whether to
   reuse an already-running daemon purely by lock-file presence + a liveness
   ping (`is_daemon_running`, `ping_fn()`). There is no fingerprint of the
   calling process's environment anywhere in this decision — a daemon started
   45 minutes ago by a completely different shell (different exported vars)
   is treated as fully interchangeable with a fresh one.
4. **The daemon executes each test in a child process that inherits the
   DAEMON's own frozen environment, not the caller's.**
   `src/app/test_daemon/light_daemon.spl:85-90` — `handle_request` calls
   `process_run_bounded(binary, ["run", ".../test_runner_single.spl", test_path, "--no-session-daemon", ...], ...)`.
   `process_run_bounded` → `rt_process_run_bounded`
   (`src/compiler_rust/runtime/src/value/sffi/env_process.rs:1159-1212`)
   builds a `std::process::Command` with no `.env()`/`.env_clear()` calls
   (only `clear_simple_child_stack_env`, which removes exactly one internal
   marker var, `_SIMPLE_STACK_SET` — line 40-42 of the same file). By Rust
   `std::process::Command` semantics, the child therefore inherits **the
   daemon process's own environment**, captured once at daemon-spawn time,
   not the environment of whichever `bin/simple test` invocation just
   submitted the request.
5. **Directly confirmed on the live daemon in this repo.** A `light_daemon`
   process (`src/app/test_daemon/light_daemon.spl`, PID 1440702) had been
   running since before this session started. `/proc/1440702/environ`
   contained **0** occurrences of `MY_PROBE_VAR` and a stale
   `SIMPLE_EXECUTION_MODE=interpret` (not the invocation's fresh value) —
   exactly the env every spec body executed through that daemon actually saw,
   which is exactly `""` for `MY_PROBE_VAR`, matching the 5/5 probe failures.

## 3. Why this is not a small fix

Propagating the invoking shell's env vars through the daemon correctly
requires **protocol changes**, not a local patch:

- The on-disk request format (`light_request_encode`/`light_request_parse` in
  `src/app/test_daemon/light_protocol.spl:23-40`) currently carries only
  `path\nexpiry_micros` — no room for env data. Adding it means extending the
  encode/parse pair and every writer (`test_submit`, `test_submit_and_wait`,
  session-scheduler batch paths in `app.test_daemon.session_scheduler`).
- Passing *all* of the caller's env indiscriminately is unsafe/unwanted (PATH,
  credentials, etc. churn per request) — a real fix needs a deliberate
  allowlist or an explicit "test env overrides" concept, which is a design
  decision, not a mechanical change.
- Applying per-request env vars inside a long-lived, single-threaded,
  request-loop daemon (`light_daemon.spl:97-109`) by mutating the daemon's
  own process env before each `process_run_bounded` call is workable (the
  loop is sequential) but changes daemon semantics: env vars set by request N
  would leak into request N+1 if not explicitly cleared, so the fix also
  needs a save/restore or explicit clear step per request.
- Alternatively, the daemon could restart itself whenever a request's env
  fingerprint disagrees with its own — but "env fingerprint" doesn't exist
  yet anywhere in `daemon_sdk`, and reintroduces the reuse-liveness decision
  described in §2.3, which is shared generic code
  (`std.daemon_sdk.client`) used by daemon types beyond the test runner (grep
  shows other `daemon_sdk` consumers), so changing its reuse contract has a
  blast radius beyond the test runner alone.

None of these is a one-file, minimal, additive change of the kind this task
asked to attempt; each requires touching the wire protocol and reuse
semantics shared with other daemon consumers. Per the task's own instruction
("if architectural, do NOT fix — file it thoroughly instead"), **no fix was
applied.**

## 4. Secondary observation (not the root cause, just a footgun noted in passing)

`env_get("MY_PROBE_VAR") ?? "MISSING"` printed `PROBE v=[]` (empty string),
not `MISSING`, on every failing run — i.e. `env_get` on a missing/absent key
returns `""`, not `nil`, so `??` never fires. Not investigated further here
(out of scope), but worth flagging since it makes "missing var" and "present
but empty var" visually indistinguishable in ad-hoc debugging, which is part
of why this bug was hard to see from spec output alone; callers should assert
directly on the raw value rather than relying on `??` to distinguish "unset"
from "empty".

## 5. Suggested fix shape (not implemented)

1. Add an optional `env_overrides: [(text, text)]` field (or a serialized
   `KEY=VALUE\n...` block) to the light-daemon request format.
2. On the client side (`test_submit`/`test_submit_and_wait` in
   `app.test_daemon.client`), capture a small, explicit allowlist of
   test-relevant vars (e.g. everything already handled by
   `propagate_env_vars` in `test_runner_config.spl`, plus any
   `SIMPLE_TEST_*`/user-declared custom vars — needs a product decision on
   scope) from the *submitting* process's env and attach them to the request.
3. In `light_daemon.spl:handle_request`, before calling
   `process_run_bounded`, `rt_env_set` each override, run the child, then
   restore (or explicitly clear) those keys so request N+1 isn't polluted.
4. Add a session-daemon regression spec that starts a daemon with one env,
   submits a request with a different env, and asserts the child saw the
   request's env — this exact bug class had no test coverage.

## Verification

- **Before:** `MY_PROBE_VAR=hello SIMPLE_EXECUTION_MODE=interpreter bin/simple test /tmp/env_probe_spec.spl` — 5/5 runs FAIL (`PROBE v=[]`, `0 passed, 1 failed`).
- **With `--no-session-daemon --no-session-share`:** 3/3 runs PASS (`PROBE v=[hello]`, `1 passed, 0 failed`) — confirms the daemon path as the sole cause.
- **No code changed** in this lane (investigation-only, per task scope). The
  regression canary
  (`SIMPLE_EXECUTION_MODE=interpreter bin/simple test test/01_unit/lib/mem/gen_arena_spec.spl`)
  was not run since nothing was modified in `src/`.

## Files referenced

- `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl:250-251` (session defaults true)
- `src/app/test_runner_new/test_runner_main.spl:218-236` (daemon routing gate)
- `src/lib/nogc_sync_mut/daemon_sdk/client.spl:26-53` (env-blind reuse decision)
- `src/app/test_daemon/light_daemon.spl:85-90` (child spawn inherits daemon's own env)
- `src/app/test_daemon/light_protocol.spl:23-40` (request wire format, no env field)
- `src/compiler_rust/runtime/src/value/sffi/env_process.rs:40-42,1159-1212` (`rt_process_run_bounded` — plain env inheritance, confirms no scrubbing beyond one internal marker)
- `src/app/test_daemon/client.spl:30-58` (`test_daemon_ensure_responsive`/`start_test_daemon_process`)

Probe file (scratch, not committed): `/tmp/env_probe_spec.spl`.
