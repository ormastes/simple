# SCV batch write design

ScvMetaInsert carries one existing schema table and its ordered values.
ScvMetaDb.insert_batch preflights schema arity/table presence and cumulative
raw value length, rejects multiline values and unsafe keys for the current
line codec, prepares canonical SdnRows and WalEntries, and calls the WAL once.
After success it mutates one local database receiver and publishes database,
WAL and sequence. No new persistence protocol is introduced.

WriteAheadLog.append_batch rejects excessive count and cumulative field size
before scanning payloads, rejects newline/CR and pipe in table/key fields,
assigns contiguous checked i64 owner sequences, CRC-encodes canonical lines,
and checks their aggregate encoded length before joining the suffix.
The legacy single-entry API shares the publication implementation while
retaining its previous size policy. Checkpoint counters publish after a
successful atomic replacement; SCV propagates its own checkpoint failure.

atomic_append_framed validates an existing header/terminal newline inside one
FileLock, creates a header only for an absent file, writes and syncs a temporary
file, renames it and releases the lock on every acquired-lease exit path.
Strict CRC prefix admission is not supplied by a header check.

Compatibility: schema remains scv-metadb-1 and canonical WAL version 2. New
batch APIs reject multiline values rather than claiming their legacy codec
can safely represent them. Existing single-row codec/replay limitations are
still open. Saved snapshots and WAL replacement are not made one crash-atomic
transaction by this change; schema migration and recovery remain required.

Verification: eight authored integration scenarios; qualified TestRunner
execution and actual cold/warm latency, maximum RSS and file-operation counts
are pending. Source structure alone proves no measured performance target.
