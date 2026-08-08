<!-- codex-design -->
# LLM Caret Messaging Architecture

## Decision

Create an MDSOC+ virtual capsule at `app.llm_caret.messaging`. The primitive room owns canonical semantics. `ChatTransportPort` and `AgentControlPort` are independent runtime-composed axes. Provider and platform names appear only in adapters/configuration.

## Layers

`domain <- port <- application <- adapter <- composition`

- Domain: IDs, identity/profile, room/message/receipt, task/artifact, capability, causal metadata.
- Ports: `ChatTransportPort`, `AgentControlPort`, `MessageStorePort`, `NotificationPort`.
- Application: room/message/profile/command/context/router/task/fallback/loop services.
- Adapters: pure-Simple SQL persistence, HTTP/streams, primitive/external transports, Claude/Codex/Gemini, plugin, MCP, legacy mailbox.
- Composition: configuration, secrets, adapter registry, cached executables, lifecycle.

## Invariants

- No adapter type crosses into domain or canonical persistence.
- A transport emits normalized events and cannot invoke an agent.
- A task begins only after routing and deduplication; `agent_update` is non-triggering by default.
- Context inclusion is ACL checked per item and recorded by ID/hash.
- Receipts separate transport evidence, agent consumption, and task handling.
- Capability fallback is data-driven; application code contains no platform-name branch.

## Persistence and hot paths

`PureDatabase` uses append-only canonical events plus materialized projections, per-room monotonic sequence, inbound dedup keys, external references, transactional outbox, dead letters, and migrations. Startup loads schema/version and enabled adapter manifests once. Hot requests use indexed `(room_id, room_seq)`, idempotency, binding/external-ID, task, and outbox lookups. Configuration and capability snapshots are cached and explicitly invalidated by plugin/config changes. External delivery is queued after commit.

The implementation imports `std.database.pure_sql.PureDatabase`, the in-tree
SQLite-compatible engine rewritten in Simple. Messaging modules must not use
`sqlite_sffi`, declare or call local `rt_sqlite_*` symbols, open C SQLite
through another language, or start a database subprocess. This
keeps connection, statement, transaction, and row handling at the repository's
embedded-database owner boundary.

`PureDatabase` describes the implementation, not a requirement to interpret its
source on every launch. The default production carrier is the fresh cached
`build/database/llm_caret_messaging_db` native executable. The optional
`build/database/llm_caret_messaging_db.smf` carrier becomes eligible when the
standalone SMF backend can lower the complete PureDatabase closure. This
rule still applies when the outer command uses `--mode=interpreter`: the outer
runtime invokes the compiled database carrier. Direct interpretation
of the database worker is an explicit diagnostic-only fallback. Artifact cache
keys include source hash, compiler identity, target, schema version, and ABI;
missing or stale artifacts fail closed or are rebuilt by the build owner.

## Security transform

Authentication, ACL, redaction, signature verification, replay protection, scoped hook tokens, rate limiting, and audit are cross-cutting transforms applied at port boundaries and before context construction. Private direct-room bodies never enter public fallback notifications.

## Agent controls

Claude and Gemini lifecycle hooks enqueue local events. Codex App Server is primary, with exact current schema verification required before adapter acceptance; hook/CLI control is fallback. `inject_context` marks consumption only after successful acknowledgement.

## Performance targets

NFR targets are calibrated from the selected realistic fixture and then frozen. Observability records startup duration, request/route/context/delivery latency, queue depth, retry/dead-letter counts, context bytes/tokens, and max RSS without logging bodies or secrets.
