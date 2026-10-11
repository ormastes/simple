# SCV WAL batch: local evidence

Scope: REQ-008, REQ-014 and REQ-024, WP3 of the user-selected 28-requirement
incremental_build_tldr_scv goal. This does not replace the full plan.

Source base: release/1.0 at 1bdffb92d6cb646fef19c27349fe27b2b7c2f8bb.

Inspected owners: src/lib/scv/metadata_db.spl,
src/lib/nogc_sync_mut/database/{wal,atomic,core}.spl.
The previous ScvMetaDb.insert copied self.db for every row, appended one WAL
entry for each row, ignored the WAL result and advanced its counter first.
The WAL append changed its entries/counter before atomic_append returned;
first append also wrote the header using a separate file lease. atomic_append
reads the entire existing log and writes a synced temporary replacement.
Batching reuses that owner rather than introducing a source-specific database,
wire format, raw app file writer or new foreign dependency.

This is local implementation research; no external performance claim or
measured speedup is asserted. Existing selected design already requires WAL
batching. No new requirements were selected automatically.
