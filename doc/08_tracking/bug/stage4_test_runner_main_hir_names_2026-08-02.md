# Stage4 test-runner main HIR names

## Reproduction

Stage4 reached `src/app/test_runner_new/test_runner_main.spl` and reported
unresolved `time_now_unix_micros`, `duration_ms`, `to_int`, and
`file_atomic_write` names.

## Fix

Time and atomic-file helpers now come from their concrete `time_ops` and
`file_ops` owners. Text conversion uses the supported optional method form.
The daemon elapsed duration is computed before the success/failure branch, so
both branches see the same value. The adjacent library runner mirror receives
the same time, conversion, and duration-scope fixes.

## Regression evidence

`test_runner_main_hir_contract_spec.spl` checks concrete owners, conversion,
scope order, and mirror parity.

## Grouped library test-runner follow-up

The same broad-facade failure shape remained across the library test-runner
subtree. The grouped repair routes directory walking through
`std.io_runtime`, time reads through the concrete `time_ops` owner, atomic
file writes through the concrete `file_ops` owner, and the system monitor's
previously undeclared raw file read through `std.io_runtime.file_read`.

Behavioral regression coverage is executable rather than a source-text
assertion:

- `test/01_unit/lib/test_runner/bootstrap_facade_owner_behavior_spec.spl`
  recursively discovers a real nested Markdown fixture and reads live system
  metrics through the repaired modules.
- `test/01_unit/lib/test_runner/source_doctest_runner_spec.spl` exercises real
  doctest extraction through `doctest_runner`, whose time, directory, and
  atomic-file dependencies now use bootstrap-visible owners.

The focused no-stub native build compiled 45 modules with 0 failures, and its
fresh executable ran 2 examples with 0 failures. The retained build log is
`build/focused-stage4-facade/logs/native-build.log`.

Bare `to_int(text)` repairs were handled by a separate non-overlapping lane;
that lane also routed `checkpoint.spl` through the concrete time owner after
the batches were integrated. `dir_walk_native` in `test_manifest_scanner.spl` remains a
similar but unproven broad-facade risk because `std.io_runtime` does not expose
that distinct native-walk surface.

## Core execution owner follow-up

The next complete Stage 4 error-collection pass proved the same broad-facade
failure for `ProcessResult`, bounded process execution, raw file size, and file
modified time in `test_runner_execute.spl`. The grouped repair routes the exact
family through `std.nogc_sync_mut.io.process_ops` and
`std.nogc_sync_mut.io.file_ops` in all seven affected modules, and removes the
unused `ProcessResult` import from `test_runner_container.spl`.

Existing behavior coverage remains the oracle for the unchanged operations:
`source_doctest_runner_spec.spl`, `process_tracker_spec.spl`,
`test_runner_tracked_wait_spec.spl`, and
`test_runner_spipe_expect_helper_spec.spl`. Final admission is the no-stub
Stage 4 full-CLI build; the isolated native owner probe was interrupted before
producing a verdict and is not recorded as PASS evidence.

## Directory creation owner follow-up

The next Stage 4 pass proved `dir_create_all` unresolved through the broad
`std.io` facade in `test_runner_coverage.spl`. The same exact family remained
in `doc_generator.spl`; both now import `std.io_runtime.dir_create_all`, and an
unused matching import was removed from `test_runner_main.spl`.

The existing coverage aggregation and system coverage specs remain the
behavioral oracle. The isolated no-stub probe was interrupted without a
verdict, so only the subsequent full Stage 4 build may admit this repair.

## Compiler warning owner follow-up

After the directory repair passed, Stage 4 reached
`test_runner_helpers.spl` and proved its active call-graph and closure warning
accessors were missing imports. The helper now imports the two concrete
compiler owners directly. A focused no-stub interpreter regression clears the
shared owner state, invokes both display helpers, and verifies both owner
accessors remain empty; it passed 1/1 before the next full Stage 4 cycle.

## Doctest cleanup owner follow-up

The next Stage 4 cycle passed the warning helpers and then proved
`file_remove` unresolved through the broad `std.io` facade in both doctest
runners. All four active cleanup calls now import the concrete
`std.nogc_sync_mut.io.file_ops.file_remove` owner alongside their existing
atomic-write dependency.

`source_doctest_runner_spec.spl` now executes a real source doctest and verifies
that its generated fixture is absent after the runner returns. The focused
no-stub diagnostic passed 2/2. Final admission remains the subsequent full
Stage 4 full-CLI build.

## Test-cache stat owner follow-up

The following Stage 4 cycle passed the doctest cleanup repair, reached 395 HIR
modules, and then proved `rt_file_stat` unresolved in
`app.test_cache_shared`. That module was importing three raw runtime symbols
through `app.io.mod`; it now uses the concrete public
`std.nogc_sync_mut.io.file_ops` wrappers for stat, text read, and write. The
adjacent read/write migration prevents the same invalid facade family from
failing on the next resolver step.

`test_result_cache_spec.spl` now records a real dependency, removes it, and
verifies the cached result becomes stale. The single focused command exited
before parsing because the Stage 3 CLI does not expose `test`; it is retained
as non-evidence. Final admission remains the next no-stub full Stage 4 build.

## Shell and process helper owner sweep

The next no-stub Stage 4 cycle passed `app.test_cache_shared`, reached 398 HIR
modules, and then proved `shell_int` unresolved through the broad `std.io`
facade in `test_runner/system_monitor.spl`. A bounded production sweep found
the same ownership defect for shell and process helpers in 65 modules across
test-runner, debug/T32/DAP, QEMU, replay, MCP, package, and process-monitor
surfaces. Those modules now import only the affected names from the concrete
`std.nogc_sync_mut.io.process_ops` owner; unrelated file and environment names
remain on their existing imports, and re-export-only facades were not changed.

`bootstrap_facade_owner_behavior_spec.spl` now executes canonical `shell_bool`
and `shell_int` behavior alongside its live system-resource assertions. The
single focused command stopped at the deployed runtime ABI probe before test
parsing and is non-evidence. Final admission remains the next no-stub full
Stage 4 build.

## Random-access file owner follow-up

The subsequent Stage 4 cycle passed the system-monitor blocker, reached 400
HIR modules, and then proved `file_size` and `file_read_text_at` unresolved in
`test_runner_async.spl`. All five adjacent file helpers in that module now
come directly from `std.nogc_sync_mut.io.file_ops`; the mutability siblings are
re-export-only facades and require no duplicate edit. The related
`test_runner_execute.spl` size/mtime pair was already on the concrete owner.

`random_access_file_owner_behavior_spec.spl` writes a real file larger than the
capture cap, verifies its exact size, and proves the async reader retains the
HEAD and TAIL while reporting the eight omitted bytes. Its single bounded
diagnostic passed 1/1, but the executable identified itself as the Rust seed;
this is supporting behavior evidence, not pure-Simple Stage 4 admission. The
next no-stub full build is the final cycle in this continuation.
