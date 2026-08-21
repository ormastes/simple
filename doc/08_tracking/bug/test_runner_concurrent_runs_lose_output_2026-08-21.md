# Concurrent `simple test` runs lose their output and exit 0 (silent false green)

- **Date:** 2026-08-21
- **Status:** FIXED
- **Severity:** critical — a test runner reporting success for a run that
  executed nothing is the worst failure mode a test runner has.
- **Area:** `src/app/test_runner_new/`, `src/app/test_daemon/light_daemon.spl`

## Symptom

Two concurrent `simple test <specA>` and `simple test <specB>` processes in the
SAME worktree could make one of them return **rc=0 with ZERO test output** — no
examples, no failure, not even a `SPEC FILE VERDICT:` line. In the reporting
lane's 2-way sharded run, **42 of 122 spec logs** came back that way. A serial
re-run of the same specs was clean.

Because every sweep in this repo scores a spec by its exit code, those 42 specs
were recorded as PASSED. Nothing anywhere said a spec had not run.

## Mechanism

Two independent defects, one producing the loss and one hiding it.

### 1. Unbounded duplicate daemons racing on one request directory

`ensure_daemon()` (`src/app/test_runner_new/test_runner_client.spl:268`) is
check-then-spawn with **no mutual exclusion**:

    fn ensure_daemon() -> bool:
        if daemon_lock_alive():
            return true
        ...spawn light_daemon.spl...

N clients that all find the lock absent all spawn a daemon, and
`light_daemon.spl:157` wrote the lock with a plain last-writer-wins
`file_write` — the losers kept running. **Measured 2026-08-21 on this host: a
6-client burst left 4+ light daemons alive**, every one of them polling the same
`.build/test_daemon_light/requests` directory.

Two daemons then race on the same `.req` file. The winner runs the spec, writes
the real response and deletes the request; the loser reaches
`light_daemon.spl:118` `read_file_text(req_path)` **after** the deletion, gets
`""`, and falls into the `test_path == ""` branch at `:121`, which
`atomic_write_text`s the stub `"1\nmissing test path"` over the winner's real
response. The client that owned the request then reads a body carrying no
verdict line and no test output at all.

This cannot be fixed from the client: the check and the spawn can never be one
atomic step out there. It has to be enforced by the only processes that can see
each other — the daemons.

### 2. The client returned the child's exit code verbatim

`print_response` (`test_runner_client.spl:293` pre-fix) parsed the response's
first line as the exit code and printed the body, then returned that code with
no check that anything had run:

    val code = content[0:newline].trim().to_i64() ?? 1
    val body = content[newline + 1:]
    if body != "":
        print body
    code

An empty body carried a `0` straight out. `run_one_direct` (`:387`) had the
identical shape on the direct lane: `if out != "": print out` … then `code`.

This is the half that made the loss silent instead of loud, and it is
lane-independent: whatever loses the output next time, it would have been
laundered into a green the same way.

## Fix

**`src/app/test_daemon/light_daemon.spl`**

- New `claim_lane()`: a daemon takes the lane by atomic tmp+rename of the lock
  and then *verifies* it still owns it; a daemon that finds a **live** incumbent
  (checked via `/proc/<pid>`) exits immediately instead of serving. Two racing
  renames are serialised by the kernel, so after the settle both losers read the
  same winner pid and stand down.
- The poll loop rechecks lock ownership every iteration and returns as soon as
  another daemon owns the lane.
- `handle_request` now returns **without writing a response** when the request
  file no longer exists. The old fall-through to `"missing test path"` is what
  clobbered the winner's real response.

**`src/app/test_runner_new/no_examples_gate.spl`** (new, importable)

Holds the fail-closed decision, for the same reason `daemon_backlog.spl` exists:
`test_runner_client.spl` is a bare-`fn main` script and cannot be imported by a
spec, so the DECISION lives where a unit spec can pin it.
`no_examples_exit_code(output, code)` rewrites `code == 0` with no
`SPEC FILE VERDICT:` line to `1`; a non-zero code is passed through untouched
(a 139 stays a 139 — the diagnosis is in that number).

**`src/app/test_runner_new/test_runner_client.spl`**

`fail_closed_on_no_examples` applies that decision on **both** lanes
(`print_response` for the daemon lane, `run_one_direct` for the direct lane) and
prints an explicit verdict:

    ERROR — 0 examples executed: <path> produced no SPEC FILE VERDICT line and exited 0

## Reproduction and evidence

| probe | pre-fix | post-fix |
|---|---|---|
| light daemons alive in one worktree after a 6-client burst | **4+** | **1** |
| 2-way concurrent loop, 20 iterations / 40 runs, silent greens | see note | **0** |
| `no_examples_exit_code("", 0)` | `0` (silent green) | `1` |

Note: the *silent-green interleaving itself* is load-dependent and did not
reproduce in a 2-way loop on this host at the time of the fix (0/40), which is
exactly why the fail-closed rule was added rather than relying on the daemon fix
alone — the duplicate-daemon race **is** directly reproducible (row 1) and is the
mechanism that loses the output.

## Guards added

- `scripts/check/check-test-runner-concurrent.shs` — fail-closed, `--selftest`
  (6 fixtures, fatal, run before every scan), verdict as the last line of
  stdout. Runs the 2-way concurrent loop and asserts (a) every run reports its
  examples — rc=0 **and** a verdict line — and (b) the lane never grows more
  than one daemon. A run that executed 0 invocations is `ERROR`, never a pass;
  every client's exit status is read directly into a variable on the line after
  the `wait`, never through a pipe. Measured post-fix:
  `PASS — 40 run(s) executed across 20 iteration(s), 0 silent, 0 failed, at most 1 lane daemon(s)`.
- `test/01_unit/app/test_runner_new/no_examples_fail_closed_spec.spl` — 12
  examples pinning the 0-examples rule, including that a real failure code is
  never masked into a generic 1.
- `test/fixtures/concurrency/conc_a_spec.spl`, `conc_b_spec.spl` — the two
  trivial specs the check drives.

## Design constraint preserved

The test-runner design from `7a6f6459a81` (daemon + backlog bypass) is
untouched: `daemon_backlog_bypass` still diverts clients away from the
single-worker queue, and the daemon lane still owns request expiry and
killed-worker verdict synthesis. The change only makes the lane single-owner and
the result fail-closed.
