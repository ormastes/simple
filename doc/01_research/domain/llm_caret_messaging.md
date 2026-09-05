<!-- codex-research -->
# LLM Caret Messaging — Domain Research

Date: 2026-08-02

## Confirmed external constraints

- Gemini CLI documents synchronous lifecycle hooks including `SessionStart`, `BeforeAgent`, `BeforeToolSelection`, `BeforeTool`, `AfterModel`, `AfterAgent`, and `SessionEnd`. `BeforeAgent` can inject additional turn context. This supports a managed settings fragment, but hook work must enqueue locally to avoid blocking the agent loop. [Gemini hooks](https://geminicli.com/docs/hooks/) and [hook reference](https://geminicli.com/docs/hooks/reference/).
- Matrix defines rooms, event streams, thread relations, read markers, public/private read receipts, and threaded receipts. Its specification also warns clients to deduplicate events received through multiple APIs. This makes Matrix a strong external contract reference while canonical cross-platform task/agent receipts remain local. [Matrix Client-Server API](https://spec.matrix.org/v1.19/client-server-api/).
- The current OpenAI documentation search available in this session did not surface the App Server protocol page. The supplied `turn/start`, `turn/steer`, `turn/interrupt`, `thread/inject_items`, and streamed event mapping is retained as a design hypothesis that must be checked against the installed/current Codex App Server schema before implementation is accepted.
- External platform read evidence is not semantically uniform. The canonical model therefore needs separate delivery, read, agent-consumption, and task-handling states, each with `native`, `local_cursor`, `synthetic`, or `unknown` evidence.

## Architectural synthesis

Use two independent extension axes:

1. `AgentControlPort`: Claude Code, Codex, Gemini, and bounded CLI fallback.
2. `ChatTransportPort`: primitive, Matrix, Slack, Teams, Telegram, Google Chat, Discord, Mattermost, LINE, KakaoTalk, and generic HTTP.

The primitive Simple room is authoritative. Every external binding publishes a versioned capability snapshot with four levels: `native`, `emulated`, `primitive_sidecar`, and `unsupported`. Application code plans behavior from capabilities rather than platform names.

## Canonical semantic decisions

- Typed IDs cover workspace, account, identity, agent, room, message, thread, task, artifact, session, binding, and delivery boundaries.
- A direct message is a room of kind `direct`; it is not a separate ungoverned message path.
- `RoomMessage` is distinct from the provider-protocol `Message(role, content)`.
- A task is distinct from its origin message and may emit state transitions and artifacts.
- Significant state transitions, not tokens or every tool call, define the default `milestones` update policy.
- Deterministic routing precedes an optional selector: explicit mention, reply target, `/assign`, unique capability match, room owner, selector, main fallback.
- Context is a bounded, reproducible manifest: policy/summary, trigger, reply chain, previous two relevant messages, unread addressed messages, profiles, task state, artifacts, and optional existing source context pack.
- Loop control uses correlation/causation IDs, hop count, triggered-agent IDs, echo hashes, turn/handoff limits, and a rule that agent progress does not wake agents by default.

## Plugin, MCP, skill, and SPipe relationship

| Surface | Responsibility | Must not own |
|---|---|---|
| Composite integration plugin | Installation, typed manifest, settings fragments, hook executables, migrations, skills, MCP declaration, ownership hashes, reversible uninstall. | Room truth or transport credentials embedded in hook files. |
| Messaging MCP | Intentional live actions such as join/send/read/who/assign/task-update/context retrieval. | SPipe documentation generation or hidden direct agent invocation. |
| Agent skills/commands | Teach Claude, Codex, Gemini, and generic agents when/how to use messaging tools and interpret receipts/tasks. | Persistence or capability truth. |
| SPipe | Requirements, executable SSpec scenarios, generated operator manuals, traceability, platform evidence classification, workflow-surface freshness, and release gating. | Runtime chat delivery. |
| Existing SPipe MCP | Existing documentation/process discovery. | Live messaging tools; keep servers separate. |

The plugin installs the runtime integration surfaces; skills describe correct use; the messaging MCP exposes live operations; SPipe proves the whole contract and keeps manuals/instructions synchronized.

## Delivery tiers

- Milestone 1: primitive server/domain, email enrollment, routing/profiles/context, three agent adapters, plugin/MCP, Matrix, Slack, Teams, Telegram, and full SPipe traceability.
- Milestone 2: Google Chat, Discord, Mattermost, generic HTTP.
- Milestone 3: genuine LINE/Kakao subsets with primitive sidecar fallback.

Live credential-backed platform gates remain independent. A simulator may prove normalization and retry logic but may not prove a platform API works.

## Security and reliability implications

- Hash short-lived email tokens; never request an email password.
- Use narrowly scoped local hook tokens, preferably over a Unix socket.
- Authenticate webhooks, deduplicate external event IDs, and preserve idempotency keys through retries.
- Enforce room ACL checks per context item and never mirror private content to public channels.
- Redact configured secrets before agent injection and record redaction-policy versions.
- Use a transactional outbox and dead-letter state; permanent failure produces one visible canonical update.

## Open questions for requirement selection

The first implementation needs user-selected answers for milestone scope, external transports included in the first release, persistence/API breadth, and measurable NFR targets. The accompanying option documents preserve these decisions without auto-selecting them.
