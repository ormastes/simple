# Misc lib spec families red — triage records (2026-09-16)

Worklist `/tmp/w_misc.txt` specs left red after easy fixes. Grouped by root
cause; each needs an owner decision before spec or lib changes.

## A. Legacy `X__method` double-underscore convention (json, mock)
- `test/01_unit/lib/std/json_spec.spl`: all 73 examples fail with
  `semantic: function 'JsonValue__parse' not found`. Current API is
  `json_parse` etc. in `src/lib/common/json/`.
- `test/01_unit/lib/std/testing/mock_spec.spl`:
  `semantic: type mismatch: cannot cast i64 to usize` at `mfn.get_call(0)`
  (`MockFunction__new` legacy plumbing).
- Unblock: rewrite both specs against the modern API (large mechanical port,
  ~73 + ~30 examples), or delete if superseded by
  `test/01_unit/lib/common/parsers_json_core_spec.spl`.

## B. Removed / moved modules
- `test/01_unit/lib/std/ml/tracking/run_spec.spl`:
  `Module "std.ml" does not export 'tracking'` — the tracking feature is gone
  from `src/lib/.../ml/` (only async_training/data_pipeline remain).
- `test/01_unit/lib/std/concurrency/promise_spec.spl`: no live
  std.concurrency; resolves to seed stdlib whose `Promise.new` is now an
  instance fn, not static (`unknown static method new on class Promise`).
- Unblock: confirm removal intent -> delete specs; else restore modules.

## C. Unbacked externs (runtime gap)
- `test/01_unit/lib/std/io/signal_stubs_spec.spl`: renamed
  `rt_signal_handler_install`->`signal_handler_install` in the spec (old name
  gone from `src/lib/nogc_sync_mut/io/signal_stubs.spl`), but now fails with
  `semantic: unknown extern function: rt_signal_install` — the backing extern
  is not registered in the runtime.
- `test/01_unit/lib/std/file/file_io_spec.spl`: `file.is_file(...)` path hits
  `unknown extern function: rt_check_file_path` (only declared in the
  seed-side `src/compiler_rust/lib/std/src/file/__init__.spl`).
- Unblock: register the externs in the runtime (or reroute the lib calls to
  the backed `rt_file_exists`/`rt_io_file_exists`).

## D. Compiler/stdlib-level semantic failures inside spec load
- `test/01_unit/lib/std/compiler/lexer_spec.spl`:
  `type 'List' does not implement required method 'iter' from trait 'Iterable'`.
- `test/01_unit/lib/std/gc_spec.spl`:
  `invalid assignment: complex indexed field receiver is not supported`.
- `test/01_unit/lib/std/core/dsl_spec.spl`:
  `unknown static method new on class ContextBuilder/DynamicProxy`.
- Unblock: language/stdlib owners decide whether these are stdlib regressions
  or obsolete spec constructs.

## E. Behavioral/content mismatches (assertion-level, not resolvable spec-side blindly)
- `editor/block_model_spec.spl` — `expected 7 to equal 6`.
- `editor/extensions/activation_hook_spec.spl`, `editor/extensions/lifecycle_spec.spl`
  (expected empty to equal "markdown"), `editor/host_simpleos_surface_contract_spec.spl`,
  `editor/office_readers_activate_before_read_spec.spl`
  (`create_slide_from_layout_id` not found),
  `nogc_async_mut_noalloc/execution/watchdog_manager_spec.spl`
  (expected true to equal false),
  `lib/pure_parser_phase1_2_spec.spl` and `lib/pure/tensor_spec.spl`
  (golden-source text drift: `expected # Simple CLI Argument Parser ...`),
  `std/compiler/loader/jit_instantiator_spec.spl`
  (`Int(1) to match Matcher(Exact(Int(0)))`),
  `std/shell/path_spec.spl` (expected empty to equal "dir").
- Unblock: per-spec owner compares expected vs current behaviour and picks the
  canonical side; several look like genuine behaviour changes never reconciled
  with their specs.
