# Target 6 compact cold graph builder

Status: pure complete-generation builder implemented; driver publication open.

`ColdHirPackageOutputV1` retains a typed semantic seed, canonical ABI bytes,
and scalar digests from frozen source and compiled outputs. It does not retain
full HIR modules or source bodies. `cold_hir_package_index_from_outputs_v1`
checks module uniqueness and admitted inventory identity, derives reverse
edges, builds real two-section export SMF records from the ABI bytes and
reverse graph, and passes the resulting artifacts through the existing
coverage, SCC, variant, action-key, and V2 generation validator. A stale ABI
payload or a missing source prevents generation construction.

The no-stub Stage2 native integration spec compiled 315 source units with
zero failures and passed 2/2 examples. It built a two-module graph with an
import and reverse dependent, rejected stale ABI bytes, and rejected a graph
that omitted one frozen `.spl` source. Build peak RSS was 1,400,464 KiB. The
326 KiB spec binary used 2,428 KiB peak RSS under a 4 GB address-space bound.
The fixture supplies digest-shaped archive fields; it does not prove that
production codegen wrote or pinned those archive bytes.

Next: the compiler driver must capture these compact receipts while typed HIR
and frozen source bytes are live, attach real post-codegen interface/action
archive receipts, verify their CAS content, call the builder, and publish the
result with compare-and-swap against the admitted binding generation. Warm
requests must then use that complete graph without a closure scan. Run the
matched native compile-time and RSS cohort before claiming Target 6.
