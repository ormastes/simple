# LLM Caret Messaging — Parallel Plan

Date: 2026-08-02
Status: Research plan; implementation waits for requirement/NFR selection

## Compiled database carrier

Build `src/app/llm_caret/messaging/database_worker.spl` into
`build/database/llm_caret_messaging_db.smf` by default, or the sibling native
executable for deployment. An outer interpreter-mode command still uses this
cached carrier. Freshness covers the entry closure, compiler identity, target,
ABI, and schema migration version; source interpretation is diagnostic-only.

## Contract freeze before fan-out

The merge owner freezes `ChatTransportPort`, `AgentControlPort`, `MessageStorePort`, `NotificationPort`, `TransportCapabilities`, `ContextBundle`, canonical event/error names, adapter-contract fixtures, manual `step("...")` phrases, and fail-fast helper placeholders. No adapter may add platform-specific canonical fields without an architecture decision.

## Parallel lanes

| Lane | Exclusive ownership | Deliverables | Dependency |
|---|---|---|---|
| Foundation | `messaging/domain/**`, `messaging/port/**`, architecture capability schema | Typed IDs/invariants, ports, events/errors, fixtures | First; contracts compile and unit tests pass |
| Primitive server | store/server adapters, room/message services | PureDatabase events/projections/migrations, API/streaming, enrollment, ACL, outbox/dedup, primitive clients | Foundation |
| Routing/profile | router/profile/command/loop guard | Names, aliases, `/who`, join, triggers, previous-message grammar, notify-all, loop prevention | Foundation; parallel with primitive internals |
| Agent integration | agent adapters, context/task services | Claude hooks, Codex App Server + fallback, Gemini hooks, session registry, context receipts, progress | Foundation and context contracts |
| Transport A | primitive, Matrix, Slack | Reference adapter and first commercial adapter | Foundation; primitive store API for integration |
| Transport B | Teams, Google Chat | Enterprise authorization/install constraints | Foundation |
| Transport C | Telegram, Discord, Mattermost, generic HTTP | Consumer/self-hosted/webhook adapters | Foundation |
| Transport D | LINE, KakaoTalk | Genuine native subset plus sidecar fallback | Capability fallback stable |
| Plugin/SPipe | plugin adapter, messaging MCP, skill/command surfaces, `doc/06_spec/**` | Safe installer, MCP tools, executable specs/manuals, skill freshness | Foundation interfaces; integrates after core vertical slice |
| Integration | composition, LLM Caret/root command routing/manifests | Composition root and cached production wrappers | Merges lanes in order below |
| Security/reliability review | review-only | Threat findings and evidence acceptance | Continuous; no feature-code ownership |

## Merge order

1. Domain and port contracts.
2. Primitive store/server.
3. Routing, profiles, tasks, and context.
4. Agent-control adapters.
5. Composite installer and messaging MCP.
6. Matrix, Slack, Teams, Telegram.
7. Google Chat, Discord, Mattermost, generic HTTP.
8. LINE and KakaoTalk.
9. Composition-root integration.
10. Live-platform evidence and traceability.

## SPipe/plugin/skill update plan

- SPipe state: `.spipe/llm-caret-messaging/state.md` records goal, ACs, lane ownership, and evidence state.
- Requirements: selected REQ-LLM-MSG-001..017 plus selected NFRs become final app documents; option files are deleted after selection.
- SSpec: executable scenarios live under `test/03_system/app/llm_caret/feature/`; generated/manual Markdown lives only under `doc/06_spec/03_system/app/llm_caret/messaging/`.
- Plugin: `plugins/llm_caret_messaging/` installs hooks/settings/MCP/skills/migrations and records ownership hashes.
- Skills: Claude, Codex, generic agents, and Gemini surfaces teach the same tool names, receipt semantics, safety rules, and fallback behavior.
- SPipe skill: `.claude/skills/spipe.md` gains only the reusable messaging evidence/freshness rule; runtime usage instructions belong in the messaging skills.
- MCP separation: `simple caret messaging mcp` exposes live chat actions; the existing SPipe MCP remains documentation/process oriented.
- Guides/reports: update the requested architecture, detail design, operator guide, feature expert, and traceability report before verify.

## Review protocol

Lower-model sidecars may audit bounded adapter matrices or manuals only after the shared contracts/helper names are frozen. The merge owner resolves conflicts. A normal/highest-capability reviewer must accept the merged research, requirements, generated-manual quality, security conclusions, exclusions, and done marks.

## Immediate next gate

The user selects one feature option and one NFR option/target process. Design then converts this research plan into architecture, detail design, executable system-test plan, and agent-task ownership artifacts before implementation fan-out.
