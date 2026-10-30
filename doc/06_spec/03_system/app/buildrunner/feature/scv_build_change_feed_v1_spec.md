# SCV bounded build change feed

Authored specification; runtime execution and generated-manual validation are pending an admitted runtime.

The feed begins at a canonically validated frozen capture. A successful expected-root publication appends one ordered snapshot pair with exact cursors. Polling the retained cursor produces all intervening events. Polling an expired, foreign, future, or disconnected cursor explicitly refuses completeness. Polling the exact current cursor proves an empty delta against that current snapshot.

Entry changes compare path, kind, mode, raw bytes, origin and producer digest. Moves emit addition and deletion because the capture DTO has no verified stable UID. Input-universe changes invalidate every membership query, including previous negative lookups. Subscribers retain only bounded cursors; slow readers expire with history rather than retaining unbounded events.

1. Freeze a complete managed input universe at cursor 0 and subscribe the build reader.
2. Publish one canonically validated source addition against the exact prior snapshot ID. The subscriber receives cursor 0 to 1, exact endpoint snapshot IDs and raw added bytes. Membership invalidation includes previously absent paths.
3. Publish the removal against cursor 1 while retaining only one event. The slow reader receives `StaleCursor`, which requires explicit resynchronization.
4. After the caller re-synchronizes to the current frozen snapshot and acknowledges cursor 2, the reader receives a verified empty `CompleteDelta`. A foreign epoch remains `UnknownCursor`.

The event ID is computed by `scv_build_feed_event_id_v1(before, after)`. It hashes a domain-separated, length-framed pair of snapshot IDs and cursors. Every payload field is already snapshot-bound; the feed accepts no caller-supplied rename or transaction metadata. Retained replay is idempotent, changed payload under the same ID is rejected, and expired replay fails explicitly. Arbitrary event IDs are rejected.

Executable system scenario: `test/03_system/app/buildrunner/feature/scv_build_change_feed_v1_spec.spl`. Focused branch scenarios: `test/01_unit/lib/scv/build_change_feed_v1_spec.spl`.

Evidence: tests committed before implementation; execution not run while runtime admission is pending. No native builder, Rust seed, watcher, scheduler, or CLI is used by this specification.

This value API performs no persistence or polling loop. The parent owns atomic publication of the returned value. Canonical validation deliberately rechecks retained snapshots before claiming continuity; its cost scales with retained payload bytes. Snapshot-pair differencing is a linear merge after canonical capture validation/copying. Event retention is limited to 1–65536 records and subscribers to 1–4096 records; the default subscriber bound is 64. Subscribers never pin event history. These are cardinality bounds, not measured RSS or latency guarantees. Production hot-path admission and performance evidence remain pending.
