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
