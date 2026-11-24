# Workaround merged-registry reader

Executable specification: `test/01_unit/app/bug/workaround_merged_registry_spec.spl`.
Requirement: `REQ-SSPEC-APP`.

Workaround refresh must validate exact registered bug IDs against the checked
legacy database plus its canonical per-bug shards. A mention in another row's
title is not a registration. The legacy file remains unchanged.

Each example creates an isolated registry through the database writer, a real
Git fixture, and an annotation. Priorities and statuses in these fixtures are
synthetic test inputs, not registrations for production bugs.

| Example | Observable requirement |
| --- | --- |
| Snapshot union | Both legacy and shard-only IDs resolve; a title-only ID does not. |
| Refresh union | A shard-only annotation publishes one matching link; legacy bytes stay identical. |
| Exact membership | An ID occurring only in a title is rejected. |
| Tombstone | A sealed empty shard removes its legacy ID from the snapshot and refresh authority. |
| Integrity | A changed shard with its old seal is rejected before a link is published. |
| Row ownership | A sealed shard containing another ID's row is rejected. |
| Pending WAL | A pending legacy WAL retains the explicit checkpoint refusal. |

`bug_snapshot_crc_spec.spl` separately protects the existing byte-domain seal
checks, including non-ASCII, CRLF, and tampered data. The all-source annotation
specification continues to require registration of every discovered annotation;
this fixture does not exempt missing production IDs.
