# SCV bounded build change feed

Authored specification; runtime execution and generated-manual validation are pending an admitted runtime.

The feed begins at a canonically validated frozen capture. A successful expected-root publication appends one ordered snapshot pair with exact cursors. Polling the retained cursor produces all intervening events. Polling an expired, foreign, future, or disconnected cursor explicitly refuses completeness. Polling the exact current cursor proves an empty delta against that current snapshot.

Entry changes compare path, kind, mode, raw bytes, origin and producer digest. Moves emit addition and deletion because the capture DTO has no verified stable UID. Input-universe changes invalidate every membership query, including previous negative lookups. Subscribers retain only bounded cursors; slow readers expire with history rather than retaining unbounded events.

Tests: `test/01_unit/lib/scv/build_change_feed_v1_spec.spl`.

Evidence: tests committed before implementation; execution not run while runtime admission is pending. No native builder, Rust seed, watcher, scheduler, or CLI is used by this specification.
