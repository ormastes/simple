# Seed interpreter mis-reads cross-module struct field (`FileHandle.id` returns 0)

Status: FIXED in the Rust seed interpreter 2026-11-05 (Lane B,
work/interp-fieldfix). Priority: P1 toolchain evidence blocker. Owner:
seed/interpreter place model.

## Corrected diagnosis (2026-11-05)

The original reading ("the cross-module field read returns 0") was a
downstream symptom. Measured with per-operation probes
(`build/test_tmp/id_probe_spec.spl`, `err_variant_probe.spl`):

- `handle.id` reads CORRECTLY at the importing call site
  (`expect(handle.id).to_equal(0x100000001u64)` passes on the unfixed seed).
- The actual defect is two-hop mutation loss in the interpreter's place
  model, same class as the Wave-3 records in
  `doc/03_plan/agent_tasks/simpleos_production_master_plan_completion_status.md`:
  1. Match-arm payload bindings are snapshots: `match driver: case RamFs(d):
     d.open(...)` mutated a copy; the callee's `driver` parameter (and the
     caller's storage) never received the container changes
     (`fd_table`/`inodes` pushes in `RamFsDriver.open`).
  2. Function-argument write-back only covered plain identifier args and
     one-level field paths. `f(table.mounts[0].driver)` — an enum payload
     nested in an array element — had no write-back at all
     (`field_receiver_path` bailed on `Index` receivers), and enum-typed
     arguments were excluded from the container merge entirely.
- Consequence: `MountTable.open` returned a handle whose backing
  `RamFsDriver.fd_table` entry was never recorded, so
  `positioned_write_bytes(handle.id, ...)` failed with `InvalidArg`
  (measured: `Err(FsError.InvalidArg)` from `RamFsDriver.write` ->
  `find_fd_idx < 0`), and `table.write(handle, ...)` failed with
  `Unsupported`.

NOTE on the diagnostic fixtures: `err_probe_spec.spl` line 16
(`table.write(handle, "hello").is_ok()`) asserts RamFs text-write, which is
`FsError.Unsupported` BY DESIGN on every engine
(`mount_driver_dispatch.spl::_driver_write_text_handle` has no RamFs arm).
That assertion is a fixture defect and stays red regardless of this fix;
staging step3/step4 (positioned write) were the real signal and now PASS
(4/4 on the fixed seed, up from 2/4).

## Fix summary (2026-11-05, work/interp-fieldfix)

- `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`:
  `merge_shared_collection_fields` gained an Enum/Enum arm (same variant ->
  merge through the payload); function-argument write-back now also covers
  enum-typed parameters and arguments addressed through general places
  (`self.mounts[i].driver`, including non-literal indices — places are
  captured at argument-evaluation time via `capture_argument_places`).
- `src/compiler_rust/compiler/src/interpreter/place.rs`: `SubjectStep`
  navigation + `merge_place_containers` (place-projection leaf merge).
- `src/compiler_rust/compiler/src/interpreter_patterns.rs`:
  `pattern_subject_binding_paths` (provenance of arm payload bindings into
  the subject), `evaluate_match_subject`, `merge_arm_bindings_into_subject`.
- Match executors wired to the merge: `exec_match_core`
  (interpreter_control.rs), `Expr::Match` (interpreter/expr/control.rs),
  and the two block-closure executors (interpreter_call/block_execution.rs).
- `src/lib/nogc_async_mut/fs_driver/ramfs.spl`: `fstat` detected directories
  with `inode.kind == RamFsKind.Dir`, which is always false (a bare
  payload-variant constructor is not a discriminant-equality operand), so
  the POSIX directory bit was never set. Replaced with a `match` (the idiom
  used elsewhere in ramfs). Previously masked: the mutation-loss defect made
  `fstat` fail early with InvalidArg, accidentally producing the expected
  error for `open_for_execute` on a directory
  (`mount_table_test.spl` "rejects a directory execute-open").
- Regression spec:
  `test/01_unit/interpreter/cross_module_struct_field_read_spec.spl` (+ fixture
  under `test/01_unit/interpreter/fixtures/`). Fails on the unfixed seed,
  passes on the fixed seed.

Verified: regression spec 2/2; staging_probe 4/4; hop probes 5/5;
`test/01_unit/interpreter` 65/65; `test/01_unit/fs_driver` 146 tests at exact
parity with the unfixed seed; `core`+`engine_divergence`+`language` 692
tests at exact parity; `bugs`+`compiler/interpreter` 1236 tests, 3 more
passing than the unfixed seed, zero regressed files.

## Original observation (2026-11-05)

Observed 2026-11-05 on x86_64 Linux host with
`src/compiler_rust/target/bootstrap/simple` as `SIMPLE_BINARY` under the
standalone phase1 test runner (interpreter mode):

- `MountTable.open("/managed-image", OpenFlags.create_write())` returns
  `Ok(FileHandle)` and `is_ok()` is `true`, but reading `handle.id` at the
  cross-module call site (spec importing `std.fs_driver.mount_table`) yields
  `0u64`. Inside the module the same handle encodes to
  `mount_handle_encode(0, 1) == 0x100000001`
  (`mount_table_support.spl:19-20`), so the stored value is nonzero; the
  cross-module field read is what returns 0.
- Consequence: any caller that must pass `handle.id` to another API
  (e.g. `MountTable.positioned_write_bytes(handle.id, ...)`, made public by
  the SimpleOS managed-container launch repair) receives `InvalidArg` on the
  seed interpreter even though the code is correct. Verified by
  `build/test_tmp/err_probe_spec.spl` and `staging_probe_spec.spl`
  (diagnostic fixtures; not part of the suite).
- Same failure class as the documented defects in
  `doc/03_plan/agent_tasks/simpleos_production_master_plan_completion_status.md`
  Wave 3 ("two-hop mutation loss is the INTERPRETER's place model";
  "cranelift AOT mis-tags cross-module method scalar returns"): value reads
  that cross a module boundary can come back tagged wrong / copied shallow.

Impact: kernel-closure specs (loader, scheduler adoption, container runtime)
cannot be honestly verified on this host until an admitted self-hosted CLI
(`bin/release/<triple>/simple`) exists; seed-run verdicts are diagnostic-only
and currently false-red for field-read patterns.

Reproduce:

```bash
SIMPLE_BINARY=$PWD/src/compiler_rust/target/bootstrap/simple \
  build/devhub-goal/phase1-testrunner/simple test \
  build/test_tmp/err_probe_spec.spl --mode=interpreter
```

Acceptance: under an admitted Stage-3/4 CLI, `handle.id` read from an
importing module equals the value observed inside `std.fs_driver.mount_table`;
`managed_workload_launch_spec.spl` then passes without fixture changes.
