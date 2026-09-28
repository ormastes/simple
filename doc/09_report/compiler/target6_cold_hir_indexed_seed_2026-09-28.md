# Target 6 indexed cold-HIR seed handoff

Status: per-entry typed-HIR admission implemented; compiler driver wiring open.

The cold compiler needs one admitted inventory digest and one source-identity
index for a whole request. Calling `cold_hir_semantic_seed_v1` per module would
recompute the complete inventory digest and search its entries each time.
`cold_hir_semantic_seed_from_admitted_entry_v1` now accepts one entry from that
admitted index, verifies the frozen HIR path and exact source bytes, computes
the typed ABI digest and canonical direct imports, and carries the already
admitted inventory digest. The existing batch seed producer calls this same
boundary after its one-time inventory digest and path-index construction.

A no-stub Stage2 native spec compiled 305 source units with zero failures and
passed 2/2 examples. It compares the per-entry result with full-inventory
admission, and proves changed source bytes, mismatched frozen paths, and a
missing inventory digest are rejected. The 260 KiB spec binary completed at
1,792 KiB peak RSS under a 4 GB address-space bound; its build peaked at
1,373,716 KiB RSS. This is correctness evidence, not a matched compile-time
or memory improvement cohort.

Next: the cold driver must admit the frozen inventory once, build a scalar
source-identity-to-entry index, call this boundary while typed HIR and source
bytes are live, retain compact semantic/ABI receipts, then attach real archive
outputs and publish a complete V2 generation. It must not retain a duplicate
full HIR plus all source contents merely to publish the index at the end.
