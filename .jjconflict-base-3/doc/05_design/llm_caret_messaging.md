<!-- codex-design -->
# LLM Caret Messaging Detail Design

## Shared types and interfaces

Typed IDs are validated non-empty tagged text values. `RoomMessage` carries canonical IDs, room sequence, thread/reply links, sender, origin, body/parts, mentions/command/audience, external/correlation/causation references, hop count, and timestamps. `TransportCapabilities` stores one four-level value per operation.

`ChatTransportPort` supplies capabilities, connect/bind/create/member/send/edit/delete/history/read/private/event lifecycle operations. `AgentControlPort` supplies capabilities, attach/resume/inject/submit/steer/cancel/subscribe/close. Initial Simple implementation uses data-plus-function adapters consistent with repository composition rather than inheritance.

## Algorithms

- Naming: normalize reserved/used names case-insensitively; prefer explicit, then persisted, else scan the lowest available ordinal.
- Routing: mention, reply, assignment, unique capability, owner, optional selector, main fallback.
- Previous context: reply chain, trigger, two prior same-thread messages, otherwise two prior non-status room messages, then bounded unread addressed messages; deduplicate and restore `room_seq` order.
- Fallback: read capability level; native executes adapter operation, emulated executes declared adapter plan, sidecar creates/uses primitive binding, unsupported returns exact error.
- Loop guard: reject self-mirror, repeated `(message,binding)`, exhausted hop/handoff/turn budgets, equivalent content within cooldown, and non-explicit progress triggers.

## Errors

Use stable text codes at boundaries: `invalid_id`, `permission_denied`, `capability_not_supported`, `duplicate_event`, `context_denied`, `context_budget_exceeded`, `agent_unavailable`, `delivery_retryable`, `delivery_permanent`, and `invalid_signature`. Preserve canonical IDs across retries.

## Embedded database implementation

`PureSqlMessageStore` composes `std.database.pure_sql.PureDatabase`, Simple's
SQLite-compatible SQL engine implemented entirely in Simple. Schema
creation and migration run once per opened database. Canonical writes use one
transaction for event, projection, deduplication key, and outbox insertion.
Room sequence allocation is persisted and monotonic. Reopening the same path
rebuilds service state from projections without replaying an external
transcript. Tests use a temporary database path or the facade's in-memory mode;
restart evidence uses a file-backed database reopened through the same facade.

## UI/API behavior

Primitive CLI/TUI/web clients show `[unread]`, `[read:local]`, `[read:native]`, `[consumed]`, `[handled]`, or `[delivery-failed]`. `/who`, `/doing`, `/status`, `/ask`, `/assign`, `/reply`, `/notify-all`, and `^` use one command parser shared by clients and MCP.

## Plugin and MCP

The integration manifest is decoded with repository SDN schema utilities. Installer changes are planned, backed up, hashed, applied atomically, checked through hook executable plus MCP initialize/tools-list, and removed only when ownership hashes still match. Messaging MCP handlers call application services; they do not bypass ACL, routing, or audit.
