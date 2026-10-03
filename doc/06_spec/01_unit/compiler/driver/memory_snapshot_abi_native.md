# Native memory snapshot ABI acceptance

Executable fixture: `test/fixtures/native_memory_snapshot_abi/main.spl`.
Lowering spec: `test/01_unit/compiler/backend/text_extern_abi_ptr_len_registry_spec.spl`.
Status: native execution and SSpec execution pending.

Compile the standalone fixture with a pinned native producer from the
patched source. Use its normal native-build entry-closure route, with
`--source src/compiler --source src/lib --entry-closure
--entry test/fixtures/native_memory_snapshot_abi/main.spl --output <binary>`.
Retain the producer SHA256, source commit/diff, binary SHA256, and build log.
Run `<binary> <absolute-absent-sink>` in a fresh process; the parent directory
must already exist and contain no symlink/reparse traversal. The companion
`<sink>.phase` must also be absent. Retain both artifacts and stdout/stderr.

| Scenario | Required evidence |
| --- | --- |
| Disabled sink | Begin returns 0 for an empty configured path |
| Semantic text ABI | Real declarations lower 1 to 2 and 17 to 20 arguments; exactly four data/length extractions |
| Memory owner | Exactly three newline-terminated records: open, snapshot, terminal; sequence 0, 1, 2 |
| Argument alignment | Snapshot source index 7, source path `src/probe.spl`, eleven cardinalities 11 through 21 in order |
| Exclusive creation | Reopening the completed leaf fails and preserves the bytes |
| Phase owner | One flushed phase record with its text fields and eleven zero cardinalities |
| Completion | Exit 0 and `NATIVE_MEMORY_SNAPSHOT_ABI_PASS` |

The fixture uses the production driver owners and runtime writer. No mock
provider or source substring assertion substitutes for native acceptance.
The known failed Windows candidate contains both double expansion and a
linked provider that returns -1 unconditionally; caller repair alone cannot
pass this native test. Keep the external process-tree guard and sampler in
the owning Windows validation run.
