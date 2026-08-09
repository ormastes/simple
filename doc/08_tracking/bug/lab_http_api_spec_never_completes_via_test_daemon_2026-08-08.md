# `lab_http_api_spec.spl` never completes under `bin/simple test` (test-daemon client times out)

**Status:** FIXED — root cause pinned and corrected; spec now completes in ~40s.
A separate, previously-masked assertion failure in the spec's own second `it`
block is now exposed and tracked as a follow-up (see "Follow-up" below).
**File:** `test/03_system/tools/simple_lab/lab_http_api_spec.spl`
**Date filed:** 2026-08-08
**Date fixed:** 2026-08-08

## Symptom

`SIMPLE_MODULE_LIMIT=4000 bin/simple test test/03_system/tools/simple_lab/lab_http_api_spec.spl`
never reaches a `Results:` verdict line. Five attempts across this session and a
prior one, all non-completion:

1. Two attempts without `SIMPLE_MODULE_LIMIT=4000` set: both hit the
   unrelated, already-known `error: runtime: Module count limit (800)
   exceeded loading ".../test_daemon/light_protocol.spl"` bug before ever
   reaching this spec.
2. One attempt, `SIMPLE_MODULE_LIMIT=4000` + no explicit outer timeout:
   killed at 900s wall-clock, `EXIT_CODE=255`, log ends mid warning-output
   with no `Results:` line.
3. One attempt, `SIMPLE_MODULE_LIMIT=4000` + `timeout 900`: ran the full
   900s, log ends with the literal line `Process timed out` (this text
   comes from `src/app/test_runner_new/test_runner_client.spl` — the test
   daemon's own client-side timeout, not the outer shell `timeout`), no
   `Results:` line.
4. One attempt, `SIMPLE_MODULE_LIMIT=4000` + `timeout 400`: same outcome —
   `exit=255`, log ends with `Process timed out` from
   `test_runner_client.spl`.

## Not host load

`test/03_system/tools/simple_lab/lab_hardening_spec.spl` — the sibling spec
in the same suite, same test file layout, same host, same session, run
immediately after attempt 4 above with the identical `timeout 400` window —
completed cleanly: `Results: 8 total, 8 passed, 0 failed`. Host load at the
time: `load average: 5.78, 6.03, 6.52` (this host has enough cores that this
is moderate, not saturating). This rules out "host is just slow right now"
as the explanation; the non-completion is specific to `lab_http_api_spec.spl`.

## Not leftover process/port state

Checked for stray `lab_server.spl` subprocess or a stale `.port` file from a
prior failed attempt that a new run might be blocking on (`start_lab_server`
in the spec, `test/03_system/tools/simple_lab/lab_http_api_spec.spl:93`,
polls a portfile written by the spawned server subprocess). Neither was
found after any of the failed attempts.

## Hypothesis (not confirmed)

`lab_http_api_spec.spl` spawns `src/app/simple_lab/lab_server.spl` as a real
OS subprocess bound to a real ephemeral loopback port
(`test/03_system/tools/simple_lab/lab_http_api_spec.spl:49-50,93`), then the
*outer* spec process itself runs under `bin/simple test`'s test-daemon
protocol (`test_runner_client.spl`). The daemon client's own timeout firing
with no partial output suggests either: (a) the spawned server subprocess
itself never signals ready (never writes/completes the portfile handshake)
under whatever is different about running through the daemon vs. a
standalone process, or (b) the daemon protocol and the spec's own
subprocess-driving I/O interact badly (e.g. inherited fds, output buffering
between the daemon's IPC channel and the spec's own process-management
code) causing the daemon side to never observe spec completion even if the
spec itself finishes.

## Suggested next step

1. Run the spec via `bin/simple run` (bypasses the daemon protocol) if that
   entry point supports directly executing a system-tier `_spec.spl`, to
   determine whether the hang is in the spec/server interaction itself or
   specifically in the daemon transport.
2. If (1) isn't viable, add a coarse stderr trace to
   `start_lab_server`/the request-loop in `lab_http_api_spec.spl` to see how
   far execution actually gets before the daemon gives up — the daemon
   timeout gives no information about which `it` block or which step was in
   flight.
3. Check `test_runner_client.spl`'s own timeout value/logic — confirm
   whether it's a fixed short client-side timeout independent of any
   `--timeout` flag passed to `bin/simple test`, which would explain why
   raising the outer shell `timeout` (900s → gave the daemon client the same
   result) had no effect.

## Evidence

- `/tmp/lab_http_api_v3.log` (this session, `timeout 400` attempt) — ends
  `Process timed out`, no `Results:` line.
- `/tmp/lab_hardening_v1.log` (this session, same `timeout 400` window,
  immediately following) — `Results: 8 total, 8 passed, 0 failed`.

## Root cause (confirmed 2026-08-08)

Not a daemon-transport issue. `test_runner_client.spl`'s own default
`--timeout` is a hardcoded `120` (line 99, `var timeout_secs = 120`),
independent of any outer shell `timeout` — this explains why raising the
outer wrapper from 900s to 400s never changed the outcome (bug doc step 3,
confirmed). But raising the *client's own* timeout with
`bin/simple test --timeout 700 ...` also did **not** help: the spec still
ran the full 700015ms and then hit `Process timed out` / `error: test-runner:
file timed out` — proving this is a genuine hang, not merely an
under-provisioned timeout.

Tracing the child `lab_server.spl` subprocess's own stdout (inherited,
unbuffered, visible in the log even while the daemon-side `it`/`step` output
stays buffered until the run completes) showed only **one** `SIMPLE_LAB_TOKEN
/ SIMPLE_LAB_LISTENING / SIMPLE_LAB_DONE` triple in the entire 700s run —
i.e. only the *first* `it` block's server subprocess ever got that far, and
the spec never progressed to the second `it` block's `start_lab_server` call.

The bug is in `start_lab_server`'s own polling loop, `test/03_system/tools/simple_lab/lab_http_api_spec.spl:133-143`:

```
var waited = 0
var bound = ""
while waited < 150000:
    if rt_file_exists(portfile):
        val t = rt_file_read_text(portfile)
        if t != nil and t.trim() != "":
            bound = t.trim()
            waited = 15000          # <-- BUG: should be 150000
    if bound == "":
        rt_sleep_ms(50)
        waited = waited + 50
```

Compare the sibling `lab_hardening_spec.spl`'s equivalent, working loop
(`test/03_system/tools/simple_lab/lab_hardening_spec.spl:127-135`), which
sets `waited = 150000` (matching the loop guard) on the same success path —
that's the correct pattern, and it's why `lab_hardening_spec.spl` (8/8) never
exhibited this hang despite spawning 8 server subprocesses.

`lab_http_api_spec.spl` has a one-digit typo: `waited = 15000` instead of
`150000`. Since the loop guard is `while waited < 150000`, `15000` never
satisfies it, so the loop keeps running — and because `bound != ""` at that
point, the `if bound == "": sleep+increment` branch (the *only* code that
would ever advance `waited` again) is also skipped every iteration. The
result: the instant the portfile is found (i.e. the moment
`start_lab_server` would otherwise succeed), the function enters an
unconditional, un-sleeping, infinite busy-spin and never returns — regardless
of how large `--timeout` is set, because it's a true infinite loop, not a
slow computation. This is why the spawned `lab_server.spl` subprocess itself
completes normally (bind, listen, serve, print `SIMPLE_LAB_DONE`) while the
*parent* spec process that's supposed to observe that success hangs forever.

### Fix

One-line fix at `test/03_system/tools/simple_lab/lab_http_api_spec.spl:140`:
`waited = 15000` → `waited = 150000`, matching the sibling spec's loop.

### Verification

`SIMPLE_MODULE_LIMIT=4000 bin/simple test --timeout 450
test/03_system/tools/simple_lab/lab_http_api_spec.spl` (post-fix):
completes in `Duration: 39724ms` (vs. hanging past 700015ms before the fix).
`Results: 4 total, 3 passed, 1 failed` — the file now reaches a real verdict
every time; it is no longer non-terminating.

## Follow-up (separate, newly-exposed defect — not this bug)

With the hang fixed, one previously-unreachable assertion now fails for real:
`it "drives the full create -> execute -> stream -> save flow over one real
server"` (test/03_system/tools/simple_lab/lab_http_api_spec.spl:303) crashes
with `semantic: array index out of bounds: index is 0 but length is 0`
somewhere in that flow (session create → execute → WS event drain → notebook
save/load). This was previously invisible because the spec never reached
that `it` block's execution report — the whole file just hung. This is a
distinct issue from the non-completion bug fixed here and needs its own
triage/bug filing; not investigated further as part of this task (out of
scope: this bug was specifically about non-termination, which is now
resolved and verified).
