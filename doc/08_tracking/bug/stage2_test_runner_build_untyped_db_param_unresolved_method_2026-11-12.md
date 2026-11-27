# Stage 2 `test_runner_build` fails: untyped `db` receiver in `update_rust_test_database` (2026-11-12)

Status: FIXED in this change (typed receiver + spec). Severity P1 (blocks Phase 4: every
suite row of the Stage 2 verification matrix is `UNSUPPORTED full-cli-artifact-not-built`
behind it, and the test runner is the only way the matrix executes specs).

## Symptom
Run 15 of the release/1.0.0 bootstrap chain (source `bfe789dd411`, Stage 2 aarch64
cranelift, `build/bootstrap-fable-15`): matrix row `test_runner_build` FAIL status=1 after
564 s. A standalone rebuild in the matrix shape (phase C argv, `SIMPLE_FILE_WORKERS=0`,
`SIMPLE_MIR_SHARD_COUNT=8`, `--threads 2`) reproduces it: rc=1, 503 s, max RSS 10.2 GB
(parent rusage), `phase=mir state=failed`, exactly one module failure:

```
[mir-lower] WARNING: unresolved method call 'update_test_result' is a FATAL lowering error
  (Task #145; const-0+rt_panic placeholder only keeps MIR well-formed) route=runtime-fallback
  module=lib.nogc_sync_mut.test_runner.rust_test_runner
[ERROR] [mir-module-failure] module=lib.nogc_sync_mut.test_runner.rust_test_runner ... fatal_count=1
[ERROR] MIR error: MIR lowering error: unresolved method call: update_test_result
  route=runtime-fallback key=::update_test_result owner= struct_method_syms=no
  record_instance_method=n/a lookup_method_in_type=no
```

## Cause
`src/lib/nogc_sync_mut/test_runner/rust_test_runner.spl:101` (twin
`src/app/test_runner_new/rust_test_runner.spl:98`):

```
fn update_rust_test_database(db, rust_result: RustTestResult, is_doc_test: bool):
    ...
                db.update_test_result(test_name, "external/rust-tests", category, category, status, 0.0)
```

`db` has no type. The seed interpreter resolves the method at run time; the pure-Simple MIR
lowering has no receiver type (`owner=` empty), so the call is unresolvable and the module
fails closed (the Task #145 rule). `update_test_result` is defined on `RunnerTestDbCore`
(`test_db_core.spl:270`, the six-argument signature this call matches), `TestDatabase`
(app twin), the compat shim and the extended database, so no unique provider exists either.

Not a compiler regression: run 13's Stage 2 (`f8ad54b28467`) fails the same minimal fixture
(`untyped_param_method.spl`: untyped param + method defined on two classes -> same error on
both run 13 and run 15 Stage 2). Run 13 linked the runner (331 modules) only because
`rust_test_runner` was NOT in its closure. `546541ef122` (`--kind` selector,
`test_kinds.spl:24 use ...rust_test_runner.{parse_cargo_test_output}`) pulled the module in
(335 modules), exposing the untyped receiver to the native lowering.

## Fix
Delete the function. `update_rust_test_database` had zero callers (only two `export` lines in the
`__init__.spl` twins; the Rust seed has its own `update_rust_test_database` in
`driver/src/cli/test_runner/test_db_update.rs`), and the standalone runner closure contains no test
database module at all. Typing the receiver instead (`db: RunnerTestDbCore`) was tried first: it
lowers, but it pulls the whole `RunnerTestDbCore` persistence closure into the runner (337 -> 354
modules: test_db_core/io/lock/parser/serializer, string_interner, test_stats, crc32, gzip crc,
csm_seal, string_builder) and both such builds (run-15 sha and the `0ceeb3c3421` tip) then died in
codegen batch 1 with `native-build worker terminated with signal 6 before producing a binary` and
no diagnostic captured, while the same 91-module DB closure builds and runs on its own
(`tests=1 suites=1`). That abort is a separate Stage 2 class (filed separately); the deletion keeps
the runner closure at 335 modules, whose codegen batches the unfixed build already ran.
Removed: the function block in both twins, the two `export` lines, the now-unused `TestStatus`
import.

## Evidence
- Red: run 15 matrix `.../verification/logs/test_runner_build.log` and the standalone rebuild
  log (scratch `s2runner/tb/build.log`, rc=1).
- Green: standalone rebuild of the deletion at `bfe789dd411` with run 15's Stage 2 (see the PR body).
  rc / elapsed / sha256).
- Non-fatal in the same log: `[hir-cache] ... stores=293 refused=42 reason=decode`, four
  `enum wire enum allocation failed` store refusals on `test_runner_main.spl` — the known
  hir-cache decode refusal class (`hir_cache_never_hits_header_rejected_2026_10_26`); HIR and
  MIR of those modules still succeed.
