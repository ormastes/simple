# Phase 1 seed: table read after a successful sqlcipher4 open fails in interpreted specs

Observed 2026-10-31 with `D:/dev/simple-phase2-rebuild-20261028/src/compiler_rust/target/bootstrap/simple.exe`,
`SIMPLE_EXECUTION_MODE=interpret`, running a `*_spec.spl` file.

Symptom: after `storage_backend_sqlcipher4_open` (or `port.open`) of
`test/fixtures/database/sqlcipher4/dense_multipage.sqlcipher4` succeeds (all nine pages decrypt, about 7 minutes),
the first `read_table` on the returned view aborts the whole file with
`error: semantic: invalid operation: tuple index access on non-tuple type i64`
(`executed=0`). Production verbs (`messenger_sqlcipher4_list_rooms`) fail the same way.

Isolation so far:
- The decrypted `view.image` is byte-identical to the generator's plaintext (0 diffs of 36864).
- `sqlite_format_read_table_bytes` on a push-built copy of that image returns the 2 room rows.
- The same read on a plaintext copy of the image, opened through the sqlite3 backend in an interpreted spec, returns 2/3/46 rows.
- In the same run, after the copy read, the module-level `val v` holding the view had become an `i64`
  (`undefined field 'image': cannot access field on value of type 'i64'`), so module-level names appear to be
  clobbered by callee locals in interpreted spec mode. Renaming spec globals with a `dn_` prefix did not cure the table read.
- The same sequence in a plain `fn main` script (JIT) works: 2 room rows, 46 message rows.

Affected, left failing/unrun: `test/02_integration/app/devhub/messenger/dense_storage_rows_spec.spl`,
`dense_pager_corruption_spec.spl`, and all `test/03_system/app/devhub/messenger/dense_messenger_*` success-path specs
except `dense_messenger_policy_and_config_spec.spl`.
Unblock: fix the interpreter defect, or run those specs on a binary that evaluates them natively.
