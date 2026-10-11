# Existing SCV owner: bounded WAL batches

The full incremental_build_tldr_scv requirements remain authoritative. This
change implements part of WP3, without declaring WP1-11 complete.

Caller -> ScvMetaDb.insert_batch -> WriteAheadLog.append_batch ->
atomic_append_framed -> FileLock / temporary write / file sync / rename.

The database domain owns rows and schema. The WAL owner numbers its entries;
the atomic owner alone performs the leased file operation. No app leaf performs
raw environment/process calls and no parallel mutation ownership is added.

All rows are preflighted before any publication. New batches have at most
4096 entries and 1 MiB of encoded suffix, with bounded raw-field scanning.
The version-2 header is created in the same lease as the suffix. Header
mismatch and a missing terminal newline reject an existing file. Failed
write/sync/rename preserves in-memory rows, entries and counters. Successful
batch mutation takes one database value receiver for all rows.

This API requires a single serialized live owner. It does not establish
cross-process sequence allocation, strict recovery, schema-v2 migration,
immutable source admission or TLDR freshness. Existing lease aging, unchecked
legacy replay, reopen sequence recovery and directory-fsync guarantees remain
unqualified owner obligations. Do not publish a freshness receipt from this API.
