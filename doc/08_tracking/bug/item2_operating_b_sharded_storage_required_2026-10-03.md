# Item 2: monolithic snapshot quota cannot satisfy Operating B

Status: OPEN. Owner: item 2 storage/index lane; integration owner Codex.
Requirements: NFR-002 through NFR-005, NFR-009. Severity: release blocker.

## Concrete source evidence

`src/lib/scv/db_snapshot.spl` and `db_identity_snapshot.spl` cap decoded
canonical bytes at 16 MiB. A million UID bindings cannot fit: each binding alone
contains a 32-character namespace and at least 32 hexadecimal actor characters,
before kind, counter, permanent alias, tombstone and framing. This is a static
capacity contradiction, not a measured latency/RSS result.

The reference reducer and identity map additionally use array scans, including
quadratic duplicate/constraint validation. A source-level record-count ceiling
of one million does not establish support for the selected million-row corpus.
The conservative fresh-incarnation-per-reservation owner also creates a durable
file per reservation and has no measured Operating B admission.

## Required repair and evidence

Implement bounded immutable shards and an indexed manifest in the existing
storage owner. Preserve one atomic manifest publication, whole accepted-batch
visibility, allocator high-water/tombstones and complete snapshot recovery;
never split a transaction into independently acknowledged shards. Queries need
persistent alias/observation indexes and bounded invalidation. Use the small
pure implementation as a semantic oracle, not as evidence of indexed scale.

Keep per-object decoding quotas; raising them to hold an entire million-row
state is not a demonstrated resource fix. Add source scenarios for a manifest
larger than one shard, corruption/missing shards, interrupted publication,
compaction preserving acknowledged state, and real full/incremental equality.

Unblock only with the selected generator/receipt, at least one million aliases
and observations, the 10,000-observation batch, three reference-machine runs,
and the unchanged latency/RSS/time/packed-size acceptance targets. Execution
remains unverified while the admitted runner is unavailable. Do not mark the
overall selected scope complete or lower thresholds based on small fixtures.
