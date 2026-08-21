# Mandatory Check Tiering Detail Design

`check-push-must-pass.shs` consumes standard pre-push ref rows. For each unique
outgoing revision it loads the manifest and ledger from that committed revision,
recomputes the source fingerprint, validates ledger cardinality/status, and runs
only conflict-tree, tree-size, conflict-marker, and quick rules gates.

`check-bootstrap-must-pass.shs` runs expensive automated manifest rows. Its
bootstrap-completion mode first requires the exact Stage 2/3 full-provenance
verdict and Stage 4 `post_bootstrap_stage4_acceptance=true` oracle, records
distinct Stage 1–4 evidence references, and then executes every automated row.
Gate logs are retained under the source fingerprint and ledger replacement is
atomic only after row evaluation completes.

Statuses are `pass`, `todo`, `blocked`, or `fail`. TODO and blocked are never
aliases for PASS. Only explicitly push-blocking rows prevent an interactive
push, allowing broad hardware/performance requirements to remain honestly open.
