# Seed interpreter mis-reads cross-module struct field (`FileHandle.id` returns 0)

Status: open. Priority: P1 toolchain evidence blocker. Owner: seed/interpreter
place+tag model (fix in pure-Simple `src/compiler`, not the Rust seed).

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
