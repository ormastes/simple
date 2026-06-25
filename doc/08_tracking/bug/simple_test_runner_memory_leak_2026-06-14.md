# Bug: `bin/simple test` runner grows unbounded RSS → OOM-killed (45–118 GB)

- **Date:** 2026-06-14
- **Severity:** P1 (kills CI containers via kernel global_oom)
- **Symptom:** Multiple `simple` processes in test-daemon containers (`docker exec ... bin/simple test <path>`) grow to 45–118 GB RSS and are OOM-killed.

## Root cause (verified by static analysis)

The OOM victim is the **long-lived parent `bin/simple test` runner process**, which itself
executes in the **no-GC ("allocate-and-leak") interpreter**. Per-spec work done *in the parent*
leaks and never reclaims, accumulating across the whole spec set (~22.5k specs) in one invocation.

This is **not** cross-spec accumulation of *interpreted-program* state: every spec runs in an
isolated child/subprocess that dies and has its memory reclaimed by the OS:

- Default mode is `fork_mode = _is_fork_available()` → true on Linux
  (`src/lib/nogc_sync_mut/test_runner/test_runner_args.spl:96`, `:490`).
- Fork path: child runs `rt_cli_run_file` then `rt_fork_child_exit` → `_exit()`; OS reclaims the
  child (`src/lib/nogc_sync_mut/test_runner/test_runner_fork.spl:36-43`,
  `src/runtime/runtime_fork.c:34`).
- Non-fork path spawns a subprocess (`process_run_timeout` /
  `process_run_with_limits`), also isolated
  (`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:45-104`).
- The C fork bridge's parent-side capture buffers are correctly reset per spec:
  `free_results()` is called at the top of `rt_fork_parent_wait`
  (`src/runtime/runtime_fork.c:74-78`, called at `:150`). Not the leak.

So the child is fine. The leak is the **parent re-allocating, per spec, in a process with no GC.**

## Accumulation site(s)

1. **Per-spec output parsing in the parent — primary churn.**
   For every spec the parent calls `make_result_from_output(...)`, which does
   `output.split("\n")` over the *entire* child stdout+stderr and builds new strings per line
   (`clean`, `error_lines`, joins, `.contains` temporaries):
   - `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl:106-128` (error extraction)
   - `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl:139-169` (pass/fail counting)
   Under no-GC every intermediate `[text]` and string here leaks. Multiply by ~22.5k specs ×
   multi-KB output each → tens of GB.

2. **Per-spec setup strings in the parent.**
   `build_coverage_wrapper` (file read/write), `build_child_args`, string-interpolated paths and
   `TestFileResult.error` strings — all allocated per spec in the parent loop
   (`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:53-104`).

3. **Result/bookkeeping arrays (bounded, NOT the cause).**
   `results: [TestFileResult]`, `completed_files` grow one entry per spec
   (`test_runner_main.spl:271, 322-345`). Bounded to ~tens of MB; ruled out as the 45 GB driver.

4. **Runtime allocator confirms no GC.** `spl_rt_malloc` is a thin tracked `malloc`; `spl_free`
   exists only for explicit deep-frees of specific containers
   (`src/runtime/runtime.c:1014`, `runtime_memtrack.h:94`). Expression-level interpreter
   allocations are never freed — as documented ("no GC, allocate-and-leak").

## Per-spec reclamation: does it exist?

- **Child:** yes — reclaimed by OS on `_exit()` (fork) or process teardown (subprocess).
- **Parent:** **no.** There is no arena reset, no `spl_free` of per-spec parse temporaries, no
  re-exec of the parent. The parent monotonically leaks for the life of one `bin/simple test`.
- A prior bisection is already in-tree: GROUPS 3–9 (container, coverage, DB, docgen, checkpoint,
  parallel, signal, closure/call-graph warnings) are commented out under `MEMORY DEBUG`
  (`test_runner_main.spl:27-70, 88-360`; `test_runner_modes.spl`;
  `test_runner_execute.spl:88,357` disables `record_coverage_sdn`). That the leak persists with
  those groups disabled points at the irreducible core loop (per-spec output parsing in the
  no-GC parent), not at coverage/DB.

## Recommended fix — ranked by impact / effort

1. **Process-per-batch (or per-spec) isolation for the parent — highest impact, low effort.**
   Re-exec a fresh `bin/simple test` parent every N specs (e.g. chunk the file list and spawn a
   short-lived child runner per chunk that `_exit()`s). The OS reclaims the leaked parent memory
   at chunk boundaries — caps RSS regardless of suite size. The test-daemon/container layer
   already shards work, so this is mostly orchestration. **Best impact:effort.**

2. **Free per-spec parse temporaries explicitly — medium effort, addresses root cause.**
   After `make_result_from_output` returns, deep-free the large transient strings/arrays it built
   (the `output` copy, `lines`, `error_lines`) via the existing `spl_free`/`spl_free_value` path,
   or restructure parsing to stream lines without materializing the full `split` array. Requires
   interpreter support to actually release interpreter-owned `Value::Str`/array buffers.

3. **Per-spec arena reset in the interpreter parent — highest effort.**
   Give the runner loop a resettable bump arena for per-iteration allocations and reset it each
   spec. Largest change to the no-GC runtime; only worth it if (1) is insufficient.

4. **Stopgap mitigations (do now):** keep using `--max-mem-gb` / `process_run_with_limits` for
   *children*, and cap the *parent* via the container cgroup; cap specs-per-invocation so the
   parent is re-spawned often (a coarse version of fix 1).

## Mitigation applied — 2026-06-22

The parent-side output parser functions in `test_executor_parsing.spl`
(`extract_error_message`, `parse_test_output`, `output_has_zero_pass_summary`, and coverage block
strip/extract helpers) now scan output line-by-line with `index_of("\n", pos)` instead of
materializing `output.split("\n")`. This does not solve the no-GC parent model, but removes the
largest per-spec `[text]` allocation named in the accumulation analysis while preserving the
existing summary/error parsing rules.

## Safe minimal reproduction (memory-capped — do NOT run the whole suite)

Demonstrate parent-side growth on a small, output-heavy set under a hard cap. The cap makes the
OOM safe (the capped process dies instead of the host):

```bash
cd /home/ormastes/dev/pub/simple
# Pick ~30 small specs that emit a lot of stdout (BDD output amplifies the leak).
ls test/**/**/*_spec.spl 2>/dev/null | head -30 > /tmp/leak_specs.txt
# Run the PARENT runner capped at 4 GB virtual; watch RSS climb across specs.
(
  ulimit -v 4000000          # 4 GB cap — parent dies safely if it balloons
  timeout 120 bin/simple test $(cat /tmp/leak_specs.txt) --no-fork 2>&1 | tail -5
) &
RUNNER=$!
# Sample parent RSS while it runs (expect monotonic growth, no per-spec drop):
while kill -0 $RUNNER 2>/dev/null; do
  grep VmRSS /proc/$RUNNER/status 2>/dev/null
  sleep 2
done
```

Expected: parent `VmRSS` rises monotonically with no per-spec reclamation. Confirm the comparison
by re-running with fork mode (default) — the *child* RSS is reclaimed each spec, but the *parent*
still climbs from output parsing. (Use a deliberately verbose/large-output spec to accelerate.)

## Key files

- `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl:106-169` — per-spec output split/parse (leak hotspot)
- `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:45-104` — parent per-spec setup
- `src/lib/nogc_sync_mut/test_runner/test_runner_main.spl:271-345` — parent spec loop + result arrays
- `src/lib/nogc_sync_mut/test_runner/test_runner_fork.spl` — fork model (child reclaimed, parent not)
- `src/runtime/runtime_fork.c:74-78,150` — parent capture buffers reset per spec (NOT the leak)
- `src/runtime/runtime.c:1014`, `src/runtime/runtime_memtrack.h:94` — no-GC allocator
