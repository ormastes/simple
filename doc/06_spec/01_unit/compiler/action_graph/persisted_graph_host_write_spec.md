# Compiler build graph host publication

This manual records the executable scenario in
`test/01_unit/compiler/action_graph/persisted_graph_host_write_spec.spl`.
Runtime qualification remains pending an admitted self-hosted compiler.

## Publish and load the exact graph

The scenario publishes an empty but valid graph, reads the exact staged graph
bytes and `CURRENT` pointer, then loads that same generation through the
production reader. It exercises the length-safe host write facade and the
existing lock, fsync, rename, and bounded read route.

```simple
val provisional = PersistedBuildGraphV1("seed", "", "snapshot-1", [])
val generation = persisted_graph_digest_v1(provisional)
val graph = PersistedBuildGraphV1(generation, "", "snapshot-1", [])
expect(persisted_graph_publish_v1(root, graph)).to_equal("ok")
expect(file_read_result(root + "/CURRENT").unwrap()).to_equal(generation)
expect(file_read_result(root + "/generations/" + generation + ".graph").unwrap()).to_equal(
    persisted_graph_encode_v1(graph))
expect(persisted_graph_load_current_v1(root).unwrap().generation).to_equal(generation)
```
