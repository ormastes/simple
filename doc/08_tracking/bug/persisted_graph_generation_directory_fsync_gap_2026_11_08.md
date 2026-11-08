# Persisted graph generation directory durability gap

Status: OPEN, source finding; crash reproduction not run.
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
