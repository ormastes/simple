# Owner-bearing operation journal startup

Source: `test/02_integration/lib/task_runner/distributed_operation_journal_open_owned_v2_spec.spl`.
Evidence: **NOT_RUN**, all three scenarios. This is a manually reviewed source
companion; no generated output or passing runtime evidence is claimed.

1. Open a real journal in a private temporary directory. Require the owned
   native generation and reject a second writer. Verify legacy close refuses
   without consuming that generation. Close through the typed port, reopen and
   reject the old copied cleanup while the replacement stays live.
2. Write a malformed real WAL CURRENT pointer. Require replay rejection and
   cleanup of the actual acquired owner. Remove only that fixture corruption
   and reopen successfully through the same owned entry.
3. Replace the retained lease bytes while the real writer is held. Require a
   retained cleanup turn and exact mismatch error. Restore the fixture's
   original bytes and retry the same cleanup capability.

Native owner regressions are authored in
`src/runtime/test/runtime_file_lock_owned_v2_test.c` and
`src/runtime/test/runtime_file_lock_owned_windows_v2_test.c`, and
`src/runtime/test/runtime_file_lock_owned_posix_unknown_v2_test.c`, also
**NOT_RUN**.
They exercise real native operations with narrowly selected compile-time fault
wrappers; they are not provider execution qualification or mocked journal
commits. See the design document for consumed, retained and unknown semantics.
