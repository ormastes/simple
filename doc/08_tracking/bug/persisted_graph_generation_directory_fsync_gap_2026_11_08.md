# Persisted graph generation directory durability gap

Status: fix-implemented-verification-pending. Fixed: generations dir fsynced (persisted_graph_sync_dir_v1) before CURRENT is published; retry with CURRENT==generation re-syncs root before ok; C rt_file_fsync on Windows now opens dirs (BACKUP_SEMANTICS). Spec: persisted_graph_host_write_spec.spl. Crash injection not run.
Severity: P2.
Found during source review of graph pointer retry candidate
`fb55b2519b8fb183348bdb60b615a15b49b81aba`.

`src/compiler/80.driver/action_graph/persisted_graph.spl` fsyncs the staged
generation file, publishes its directory entry through
`file_publish_noreplace_raw`, then publishes CURRENT and fsyncs the graph
root. It does not explicitly fsync the `generations` directory. Subject to
the actual provider's rename durability guarantees, a crash may retain
CURRENT but lose the generation directory entry it names.

This behavior predates the retry repair; it is not an introduced regression
or a verified crash. Before implementing a durability repair, review the
provider contract for `file_publish_noreplace_raw` and directory fsync on
each supported host. Verify write ordering and failure propagation with
controlled failure/crash injection, and retain a real reopen/read result.
No runtime tests, publication, or pass count is claimed here.

A related pre-existing retry ordering gap also warrants verification: if the
CURRENT rename succeeds but the following root-directory fsync fails, a retry
can see CURRENT already equal to the generation and return `ok` without
retrying that directory fsync. Neither this finding nor the generations-
directory gap is repaired by the pointer retry change.
