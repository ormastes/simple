<!-- codex-research -->
# LLM Caret Messaging Platforms — Consolidated Recommendation

Date: 2026-08-02
Status: Research input; requirements not yet selected

## Recommendation

Add `llm_caret_messaging` beside the existing LLM provider and agent-team code. Preserve `AgentTeamMailbox` as a lightweight compatibility/test API. Do not add chat platforms to `provider.spl`, and do not turn the LLM compatibility server into a room server.

The primitive Simple room defines complete semantics. External platforms advertise versioned capabilities and use native behavior when truthful; unavailable features use a bound primitive shadow room or fail with a precise capability error. Agent-control adapters and chat-transport adapters are independent.

## Target model

Domain entities: workspace, account, identity, agent profile, room, room message, receipt, task, artifact, binding, context manifest, ACL, and audit event. Public IDs are typed. Direct messages are ACL-protected rooms. Provider protocol messages remain separate from room messages.

Ports:

- `ChatTransportPort`
- `AgentControlPort`
- `MessageStorePort`
- `NotificationPort`

Application services own room/message/profile/command/context/routing/task/fallback/loop behavior. Adapters own SQLite, HTTP/SSE/WS, Claude/Codex/Gemini lifecycle bridges, external chat APIs, the composite installer, and legacy mailbox compatibility. Composition owns configuration, credentials, processes, and plugin loading.

## Functional baseline

The accepted feature set to present for selection is the supplied REQ-LLM-MSG-001 through REQ-LLM-MSG-017 list: email enrollment; room lifecycle; history/cursors; stable agent naming; mentions/keywords; main/subagent routing; bounded context injection; updates/replies/receipt tags; profile queries; join announcements; notify-all; primitive completeness; SPipe/skill integration; collaboration semantics; private messaging; a Simple message server; and native-first fallback.

Truthful receipt stages are `accepted`, `transmitted`, `delivered`, `read`, `consumed_by_agent`, `handled`, and `failed`, paired with evidence `native`, `local_cursor`, `synthetic`, or `unknown`.

Agent names persist as explicit name, existing profile name, or `role-provider-ordinal`; reserved aliases and case-insensitive collision handling are required. Routing is deterministic before an optional selector. Room updates default to task milestones. `^` targets the previous eligible message, while explicit short IDs handle concurrent ambiguity. “Previous couple” defaults to two relevant messages.

Context construction is deterministic, access-checked, redacted, budgeted, and recorded as IDs/hashes. It uses the existing source context subsystem for repository context rather than creating another index.

## Agent controls

- Claude: lifecycle hooks register sessions/profiles, inject context, gate tools, normalize task/subagent events, publish results, and persist cursors. Hooks enqueue to a local handler and return quickly.
- Codex: App Server is the intended primary protocol for starts, steering, injection, interruption, and streamed events; CLI hooks are a bounded fallback. Exact protocol method names remain an implementation-time schema verification gate.
- Gemini: managed lifecycle hooks inject context and normalize tool/model/agent events. Installation records before/after hashes and removes only plugin-owned settings.

## Transports

Primitive is Tier 0 and complete. Matrix is the external reference adapter. Slack, Teams, and Telegram are first-milestone commercial/user adapters. Google Chat, Discord, Mattermost, and generic HTTP follow. LINE and KakaoTalk implement only genuine native subsets after sidecar fallback is stable.

No adapter invokes an agent. It emits canonical inbound events. No application service checks a platform name to decide behavior; it checks capability levels.

## Persistence and API

Use SQLite append-only events plus projections, per-room sequence, inbound deduplication, external-ID mapping, transactional outbox, dead letters, migrations, and audit records. Expose versioned REST endpoints for invites/sessions, rooms/members/messages/cursors, direct rooms, profiles/agents/bindings, tasks, streaming, and webhooks. All writes accept idempotency keys.

The command family is `simple caret messaging serve|mcp|plugin`. The messaging MCP provides `chat_join`, `chat_leave`, `chat_send`, `chat_read`, `chat_mark_read`, `chat_who`, `chat_open_private`, `chat_notify_all`, `chat_assign`, `chat_task_update`, `chat_publish_artifact`, and `chat_get_context`.

## Integration package

`plugins/llm_caret_messaging/` owns a versioned integration manifest, configuration schema/defaults, agent-specific hook fragments/executables, MCP declaration/server, skills, migrations, and README. Installation must merge, back up, record ownership/hashes, verify executables and MCP discovery, and uninstall only owned entries. Transport secrets are indirect credential references.

## SPipe evidence

Unit tests cover IDs, naming, mentions, commands, context selection/budget, routing, fallback, receipts, loop guards, and permissions. Every transport runs one adapter contract. System tests use the real primitive server, SQLite, HTTP/stream path, and hook executables for the 25 supplied scenarios, including restart, idempotency, retries/dead letters, cross-room denial, private leakage prevention, loop prevention, redaction, and cancellation.

Generated manuals live under `doc/06_spec` as Markdown only. Claude, Codex, generic-agent, Gemini, SPipe, feature-expert, guide, state, and traceability surfaces must remain fresh. Unavailable live-platform gates remain explicit blockers/unsupported rows; simulator results are not promoted.

## Source layout and sequencing

Use `src/app/llm_caret/messaging/{domain,port,application,adapter,mcp}` plus `config.spl`, `composition.spl`, and `main.spl`, merging tiny types when compile cost warrants it. Freeze domain/port contracts first; then primitive persistence/server; routing/profile/task/context; agent adapters; plugin/MCP; transports; composition; live evidence.

See `doc/03_plan/app/llm_caret/messaging.md` for exclusive ownership and merge order, and the feature/NFR option documents for the decisions that still require user selection.
