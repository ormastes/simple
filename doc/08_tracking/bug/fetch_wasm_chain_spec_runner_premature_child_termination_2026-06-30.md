# Bug: `browser_session_fetch_wasm_chain_spec.spl` file-level FAIL despite 250/250 passing

- **Date:** 2026-06-30
- **Status:** FIX PR pending — "wait verification" (host-side native verification pending)
- **Component:** test runner (`src/app/test_runner_new/`) — NOT the js/web library under test
- **Severity:** Medium (false-negative test result; the code under test is correct)
- **Spec:** `test/01_unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl` (250 it-blocks, ~6370 lines)

## Symptom

`bin/simple test test/01_unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
reports `Files: 1, Passed: 0, Failed: 1` (file-level FAIL). The captured child
output contains only a partial prefix of `✓` lines (observed **111, 122, and 123**
across separate runs — non-deterministic) with **no `✗` failures** and **no
`N examples, M failures` BDD summary line**. The child exits non-zero with no
panic/abort text. Duration ~64s.

## Evidence the spec and library are CORRECT

Run directly in the interpreter, the spec passes in full, deterministically:

```
bin/release/x86_64-unknown-linux-gnu/simple run <spec>
  -> 250 examples, 0 failures   (exit 0, ~104s, peak RSS 315 MB)
```

Replicating the runner's exact child command (the runner uses
`build_child_args` => `["run", <spec>]` wrapped by `process_run_timeout_unix`
=> `timeout 120 simple run <spec>`) with output captured through a pipe also
passes in full:

```
( timeout 120 simple run <spec> 2>&1 | cat )
  -> 250 examples, 0 failures   (exit 0)
```

The 124th it-block (the first one missing its `✓`, `compares compileStreaming
and instantiateStreaming memory maximum failures in browser scripts`, spec line
4271) **passes in isolation** when extracted into a standalone spec.

## Ruled out

- **Not a per-block defect:** block 124 passes alone; the spec passes 250/250 via `simple run`.
- **Spec/library reliably correct out-of-runner:** `timeout 120 simple run <spec> | cat`
  ran **5/5 times = 250/250, exit 0** (peak RSS stable ~311-315 MB, ~104s). The
  non-determinism does **not** live in the interpreter/library.
- **Not host OOM:** host had **119 GB free** during the failing run; no `dmesg` oom-killer event.
- **Not a cgroup OOM:** `memory.max` is `max` (unlimited) at every level of the
  process's cgroup-v2 hierarchy (`user.slice` → … → `tmux-*.scope`). The child's
  ~315 MB cannot trip a cgroup limit because there is none.
- **Not the runner's own memory limiter:** default path has `max_mem_gb = 0` and
  `max_procs = 0`, so `run_test_file_interpreter` takes the plain
  `process_run_timeout` branch (no `process_run_with_limits`); the failing output
  contains **no `Memory limit exceeded` string**, so that mechanism never fired.
- **Not the 120s timeout:** child stops at ~64s, well under the 120s budget; exit code is not the timeout marker (124/-1).
- **Not a pipe-buffer deadlock:** total child output is only ~21 KB (≈10.9 KB at block 122), far below the 64 KB pipe buffer.
- **Not infix-matcher preprocessing:** the spec uses method-form `expect(x).to_equal(y)`, so `preprocess_infix_matchers_only` is a no-op (temp == original).
- **Not the SMF/compile path:** default mode is `TestExecutionMode.Interpreter` (`run_test_file_interpreter`). (Separately, `simple compile <spec>` fails with `semantic: undefined identifier: NATIVE_PROMISE_THEN` — a distinct compile-mode resolution gap, see below.)

## Root cause — mechanism undetermined; spec proven correct out-of-runner

The failure reproduces **only** when launched through `bin/simple test` (the
test-runner parent), and **never** when the identical child command
(`timeout 120 simple run <spec>`, with or without a captured pipe) is run in
isolation (5/5 clean). The child stops non-deterministically at 111/122/123 of
250 blocks with no `✗`, no BDD summary, no panic text, and a non-zero exit.

The exact kill mechanism is **not confirmed**. The obvious memory explanations
are ruled out above (no host OOM, no cgroup limit, runner memory-limiter not in
the default branch). Remaining hypotheses, none verified:

- A background sampler/monitor the test-runner parent starts for the run
  (`test_runner_resources.spl` `default_resource_limits` memory_mb_limit 512 /
  cpu 200%; `system_monitor.spl` / `process_monitor.exceeds_limits`) that
  signals the child outside the `process_run_with_limits` path — would explain
  the sampling-race-shaped non-determinism, but I did not confirm it is wired
  into the default single-file interpreter run.
- An output-capture / child-reaping race in `rt_process_run` under the
  test-runner parent's process state.

What is certain: this is a **test-runner / harness interaction with a
long-running, memory-growing (no-GC) child**, not a defect in the
`std.gc_async_mut.web.browser_session*` or `std.nogc_sync_mut.js.engine` code
exercised by the spec. To confirm the mechanism, capture the failing child's
exit status as seen by the runner (137 ⇒ SIGKILL) and check whether the runner
spawns a monitor thread for the default interpreter path.

## Reproduction

```
# FAILS (file-level), non-deterministic ✓ count:
bin/simple test test/01_unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl

# PASSES 250/250 (identical child command, isolated):
bin/release/x86_64-unknown-linux-gnu/simple run \
  test/01_unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl
```

## Suggested remedies (test-runner scope — not attempted here)

1. Verify/raise the per-child resource-monitor ceiling for the default
   interpreter path (the child legitimately needs ~315 MB; a 512 MB sampled
   ceiling on VSZ would explain the kill), or exempt single-file runs from the
   watchdog.
2. When the child is killed by the harness watchdog, record an explicit
   `error` (signal/limit reason) in `make_result_from_output`
   (`test_executor_parsing.spl`) instead of a bare non-zero exit, so this class
   of false-negative is diagnosable.
3. Optionally split this 250-block / 6370-line spec into smaller files so each
   child stays well under any sampled ceiling (mechanical; preserves all
   assertions).

## Related compile-mode gap (separate, lower priority)

`simple compile <spec>` => `semantic: undefined identifier: NATIVE_PROMISE_THEN`.
The identifier is defined and exported from
`src/lib/nogc_sync_mut/js/engine/runtime.spl`; it resolves in interpreter mode
but not in compile mode. This does not affect the default interpreter test path
but blocks `--mode=native/smf` for this spec. Tracks with the known
"compile-mode false-greens / SSpec compile pipeline" fragility.

## Fix 2026-11-05 (wasm-fixes lane) — per-child default budget 120s -> 900s

Reproduced at this branch tip on the aarch64 host. Two distinct mechanisms
were at play historically, and the second one was still live:

1. (Historical, already mitigated before this lane.) The non-deterministic
   ~64s kills with 111/122/123 lines were the host-wide
   `scripts/resource/kill_simple_monitor.shs` CPU-spin guard back when its
   `MIN_AGE_SECS` default was 60s (raised to 900 on 2026-08-17). The runner
   now also propagates its budget into the child env
   (`SIMPLE_TIMEOUT_SECONDS`, raise-only), which the monitor reads live.

2. (Fixed here.) The 2026-08-17 raise of the client default to
   `CLIENT_DEFAULT_TIMEOUT_SECS = 900` never reached the direct-dispatch and
   single-file lanes, which still hardcoded 120s:
   - `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl`
     (`parse_test_args`, `var timeout = 120`) — feeds
     `TestOptions.timeout`, the budget `run_test_file_interpreter` hands to
     `process_run_timeout`/`process_run_with_limits`. This is the path
     `bin/simple test <file>` takes when the session daemon is unavailable
     ("running directly [fallback]").
   - `src/app/test_runner_new/test_runner_single.spl` (`parse_child_run`)
     and its std twin `src/lib/nogc_sync_mut/test_runner/test_runner_single.spl`.

   Measured on this host (aarch64 seed, interpreter/JIT): the spec's honest
   direct run is 250/250, exit 0, but takes ~586s wall / ~873 MB RSS — far
   above the 120s lane budget, so the runner killed the child at
   `budget_ms=120079` with no BDD summary: a DETERMINISTIC premature
   termination, the stable remnant of this bug.

   Fix: all four per-child defaults now agree at 900s (the app single lane
   derives its default from `client_default_timeout_secs()`, so
   `SIMPLE_TIMEOUT_SECONDS` keeps working there; the std twins carry the
   literal with a sync comment). 900 matches `KILL_SIMPLE_MIN_AGE_SECS`, so
   the per-spec budget and the runaway reaper no longer race.

3. (Also fixed here — exposed by raising the default.) `run_scoped_child`
   (`src/lib/nogc_sync_mut/test_runner/native_owned_process.spl`) overwrites
   the resource-scope wall budget with the per-file timeout but kept the
   UNIT-class CPU budget at its default 600s. A single-threaded child
   legally using its 900s wall grant therefore always tripped the smaller
   CPU budget and died as "Declared resource budget exceeded" at ~600s —
   the raised timeout was still a lie. New `scoped_cpu_budget_ms` helper
   keeps the CPU grant >= the wall grant (0 = inherit stays disabled).

Evidence:
- RED (pre-fix): `simple test test/01_unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
  -> `timeout=1 reason=aggregate-lane-timeout budget_ms=120079`,
  `Results: 1 total, 0 passed, 1 failed, 1 timed out (unverified)`.
- RED (pre-fix, new pin spec):
  `test/01_unit/app/test_runner_new/direct_lane_timeout_default_spec.spl`
  -> 1 passed, 3 failed (default still 120).
- GREEN (post-fix): same pin spec 4/4; affected spec run through the runner
  to completion with 250/250 (repeated runs — see PR body).

Post-fix end-to-end (source-mode runner — the phase1-testrunner binary in
this environment is a frozen native build predating the fix, so the runner
was executed from the worktree sources:
`SIMPLE_LIB=src $SEED run src/app/test_runner_new/main.spl test <spec> --mode=interpreter`):
- resource scope ACTIVE (default limits): 250 total, 250 passed, 0 failed,
  601.6s — past the old 600s CPU tripwire that previously reported
  "Declared resource budget exceeded".
- `--no-limits` probe: 250 total, 250 passed, 0 failed, 606.4s.
Both deterministic full completions with the BDD summary intact.

Note: 873 MB child RSS is far below both the 16GB `process_run_with_limits`
ceiling and the monitor's 24GB RSS guard, so no memory limiter fires; this
was purely the wall-clock default. The unrelated Rust-seed JIT panic
("can't resolve symbol simple_contract_check" in cranelift finalize, seen
once adjacent to a timeout kill) is a separate seed defect, not this bug.
