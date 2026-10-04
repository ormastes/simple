# Evidence digest streaming compatibility

Source: `test/01_unit/lib/scv/db_evidence_stream_spec.spl`.
Manual intent, 2026-10-04. Native execution/docgen: **UNRUN**.

- Preserve domain and chunk state against independent fixed envelope SHA-256.
- Match canonical envelopes across binary partitions; inspect owner counters.
- Reject duplicate and noncanonical dependency identities.

Run this source with `<runtime> test <spec> --native` and generate its canonical
manual with `<runtime> spipe-docgen <spec> --output doc/06_spec --no-index` after
runtime admission. Require zero stubs; this manual supplies no execution PASS.
