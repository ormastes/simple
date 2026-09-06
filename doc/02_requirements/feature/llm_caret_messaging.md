# LLM Caret Messaging — Feature Requirements

Date: 2026-08-02
Selection: Feature Option A

- REQ-LLM-MSG-001: Enroll a local account through a hashed, single-use, expiring email verification token; external identities bind through their native authorization flow.
- REQ-LLM-MSG-002: Create, inspect, and manage canonical public, private, direct, channel, and task rooms with membership and ACL enforcement.
- REQ-LLM-MSG-003: Store ordered room messages and expose paginated history plus separate accepted, transmitted, delivered, read, consumed-by-agent, handled, and failed receipts with truthful evidence classification.
- REQ-LLM-MSG-004: Allocate and persist stable explicit/profile/generated `role-provider-ordinal` agent names with reserved-name and case-insensitive collision handling.
- REQ-LLM-MSG-005: Normalize native mentions and parse canonical names, aliases, configured keywords, replies, `/ask`, and `/assign` while ignoring escaped/fenced text by default.
- REQ-LLM-MSG-006: Bind main, subagent, advisor, and router handlers and route deterministically before any optional selector.
- REQ-LLM-MSG-007: Build ACL-checked, redacted, budgeted, reproducible context manifests from policy, summaries, trigger/reply history, two prior relevant messages, unread addressed messages, profiles, tasks, artifacts, and optional existing source context packs.
- REQ-LLM-MSG-008: Expose milestone/verbose/final-only/silent task updates, replies, previous-message commands, and truthful receipt tags.
- REQ-LLM-MSG-009: Support `/who`, `/doing`, and `/status` profile/task queries.
- REQ-LLM-MSG-010: Emit structured join events containing stable name, role, capabilities, handler, and current task.
- REQ-LLM-MSG-011: Implement permission-controlled `@all` and `/notify-all` through safe native mention or primitive fanout with rate limiting.
- REQ-LLM-MSG-012: Make the primitive Simple room the complete reference implementation and optional shadow room for external bindings.
- REQ-LLM-MSG-013: Supply a versioned composite integration plugin, dedicated messaging MCP, aligned Claude/Codex/agent/Gemini skills and commands, executable SSpec, generated manuals, feature expert, guide, state, and traceability report.
- REQ-LLM-MSG-014: Separate messages, tasks, artifacts, progress, handoffs, and terminal states and prevent echo/self/progress-trigger loops.
- REQ-LLM-MSG-015: Represent private messages as ACL-protected direct rooms, using native DM only when capability truth permits and never leaking content into a public channel.
- REQ-LLM-MSG-016: Provide `simple caret messaging serve` with the in-tree pure-Simple `PureDatabase` SQLite-compatible engine, events/projections, migrations, per-room sequence, idempotency, deduplication, transactional outbox, dead letters, audit, REST, SSE, optional WebSocket, and scoped authentication. Normal and interpreter-hosted launches use a fresh cached SMF/native database carrier.
- REQ-LLM-MSG-017: Drive all transport behavior from versioned `native`, `emulated`, `primitive_sidecar`, or `unsupported` capabilities; ship primitive, Matrix, Slack, Teams, and Telegram first, followed by Google Chat, Discord, Mattermost, generic HTTP, LINE, and KakaoTalk on the same contracts.

## Compatibility invariants

`AgentTeamMailbox`, provider-protocol `Message`, `provider.spl`, the compatibility completion server, and the SPipe documentation MCP keep their existing roles. External adapters never invoke agents directly. Simulator evidence never qualifies as live-platform evidence.
