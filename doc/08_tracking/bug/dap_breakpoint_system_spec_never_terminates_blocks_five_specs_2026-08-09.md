# `dap_breakpoint_system_spec` never terminates — CAUSE ESTABLISHED

**Status:** FIXED 2026-08-09 (stream G3) — cause established by direct measurement
**Found:** 2026-08-09 by stream P3 (host `DebugTarget` adapter)
**Component:** `test/03_system/tools/dap/*_system_spec.spl` (family of four)

## Cause

There is no signal, no lock, and no deadlock. **The spec is simply asked to do
about 70 hours of work.**

`simple check` costs **~100 seconds of CPU per file**, and `simple check <dir>`
spawns **one worker process per file** (`src/app/cli/check_entry.spl:184-189`
loops `expand_check_targets()` and runs `simple run src/app/check/main.spl
<one-file>` for each). The per-file spawn is deliberate — see the comment at
`check_entry.spl:14-19` — so the cost is linear in file count with no
amortization.

Measured on `x86_64-unknown-linux-gnu`, 2026-08-09:

| command | result |
|---|---|
| `bin/release/x86_64-unknown-linux-gnu/simple run src/app/check/main.spl <1 file>` | **1m41.8s**, exit 0 |
| `bin/simple check <1 file>` (no `SIMPLE_TIMEOUT_SECONDS`) | killed at 68s by `kill_simple_monitor`, exit 255 |
| `bin/simple check src/lib/nogc_sync_mut/dap` (19 files) | still running at 5m, per-file kills |
| `... main.spl <2 dirs, 35 files>` in ONE process | still running at 10m — batching does not help |

The spec's second example targeted **`src/app` = 2,544 `.spl` files**, i.e.
2,544 × ~100s ≈ **70 hours**. That is the "never terminates".

The whole family had the same defect, just with smaller (still unbounded)
targets, so fixing only the breakpoint spec would have moved the block to the
next one:

| spec | old target | files | est. runtime |
|---|---|---|---|
| `dap_breakpoint_system_spec` | `src/app` | 2544 | ~70 h |
| `dap_stack_trace_system_spec` | `99.loader` + `95.interp` + `80.driver` | 174 | ~4.8 h |
| `dap_variables_system_spec` | `30.types` + `35.semantics` | 176 | ~4.9 h |
| `dap_stepping_system_spec` | `95.interp` + 1-in-5 of `10.frontend` | ~40 | ~1 h |

## Leads that were WRONG

- **Not signal 16.** Exit 144 is not reproducible from the spec itself. Observed
  exit codes are 255 (worker SIGTERMed by `kill_simple_monitor` at the 60s CPU
  budget) and 143/124 from an outer wrapper timeout. 144 was most likely the
  reporting harness's own wrapper, not anything the spec or the runner raises.
- **Not `pkill -f` self-match.** There is no `pkill` anywhere in
  `src/app/test_runner_new/`, `src/app/test_daemon/`, or the DAP specs. The only
  `pkill -f` uses in `scripts/check/` are unrelated WM/QEMU gates.
- **Not an unbounded retry in the runner.** `src/app/test_runner_new/` and
  `src/app/test_daemon/` contain no retry loop for a spec file. The observed
  "retries indefinitely" was a wrapper outside the runner. No retry cap was
  therefore added — there is nothing to cap.
- `kill_simple_monitor` **is** involved, contrary to the earlier note: its log
  names the *worker child* (`simple run src/app/check/main.spl <file>`), never
  the spec, which is why a grep for the spec name found nothing.

## Fix

Each of the four specs now checks a **capped file list** (`MAX_CHECK_FILES = 2`)
instead of a directory, so worst-case runtime is stated up front. The breakpoint
spec's out-of-scope `src/app` whole-tree target was replaced with `src/app/dap`,
which is what its own `@cover` header names.

The cap is per-spec, sized against a hard ceiling discovered while verifying:
**the test daemon kills a spec at 600s** with `Process timed out`, exit 255, and
**no verdict line** — the same "reads as not-yet-run" failure mode in miniature.
`dap_variables_system_spec` hit it at 2 files (>630s), so its cap is 1. Measured
wall times after the fix: breakpoint 7m21s (4 files), stack_trace 8m45s (2),
stepping 1m19s (2).

Sampling was reduced, not removed: a directory-wide parse gate at ~100 s/file is
not something a spec can carry. If tree-wide parse coverage is wanted it belongs
in a dedicated gate, and it needs `simple check` to stop paying full interpreter
startup per file first.

## Follow-on defect (separate, not fixed here)

`simple check` costs ~100 s of CPU for a single file — dominated by loading the
checker itself from source (`simple run src/app/check/main.spl`), and batching
35 files into one process did not amortize it. Until that is addressed, no gate
can parse-check a directory of any size, and `bin/simple check <anything>` is
unusable under the default 60s `kill_simple_monitor` CPU budget without
`SIMPLE_TIMEOUT_SECONDS`.

## Corrections to the original report

Two of the five "blocked" specs do not exist:
`test/03_system/tools/dap/breakpoint_system_spec.spl` and
`test/03_system/tools/dap/dap_protocol_live_spec.spl`. The directory holds five
spec files, of which four are the affected family plus `dap_spec.spl`.

## Related

- `doc/08_tracking/bug/lab_http_api_spec_never_completes_via_test_daemon_2026-08-08.md`
- Environment trap confirmed again: a stale `.build/test_daemon_light/daemon.lock`
  makes EVERY spec exit 1 with `ERROR: test daemon timed out` and no verdict
  line. Fix: `rm -rf .build/test_daemon_light`.
