# SCV identity map candidate allocation

Executable: `test/01_unit/lib/scv/distributed_identity_map_spec.spl`.
Requirement: REQ-004 in `simple_distributed_textual_databases` (partial).

This manually maintained scenario companion describes pure candidate-state
transitions. It does not demonstrate durable settlement, transport admission,
signed receipts, concurrent writers, or a production database.

| Scenario | Steps | Expected outcome |
|---|---|---|
| Retry a permanent alias | Allocate an offline identity; retry it | Sequence stays 1, one binding remains, original empty state stays empty |
| Retain tombstones | Allocate and tombstone the first identity; allocate another | New sequence is 2, old reverse identity remains, retry stays tombstoned, original state stays live |
| Isolate kinds and namespaces | Allocate bug and test kinds; submit a foreign namespace | Each kind starts at 1; rejection preserves both bindings and next bug sequence |
| Retain high-water state | Restore high-water 41 with no live rows; allocate; try exhausted u64 | Next sequence is 42; exhausted allocation rejects without wrapping |
| Reject regression | Remove high-water from a state with an accepted binding; submit new identity and retry | Both return `SCVDB_ALLOCATOR_REGRESSION` |
| Reject duplicate forward/reverse rows | Combine independent candidates sharing an alias; duplicate an identity row | Allocation and tombstone reject ambiguity; reverse lookup refuses a first-row answer |
| Reject relabeled namespace | Move bindings under another namespace header | Reverse lookup returns no identity |

Phase-1 diagnostic execution reported seven executed examples and seven passes
on Windows. SPipe production execution and automatic docgen remain unverified.
