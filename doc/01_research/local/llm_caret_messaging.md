<!-- codex-research -->
# LLM Caret Messaging — Local Research

Date: 2026-08-02

## Finding

The requested feature is a new bounded context, not an incremental extension of the current provider or agent-team types. The repository has useful seams, but its existing objects intentionally stop before durable, concurrent, transport-backed messaging.

## Existing surfaces and decisions

| Surface | Repository evidence | Decision |
|---|---|---|
| Agent mailbox | `agent_mailbox.spl` stores an immutable `[AgentTeamMessage]`; messages contain `from_agent`, `to_agent`, `channel`, and `body`. | Preserve as compatibility/test API. Add a legacy adapter after canonical messaging exists. |
| Planning | `agent_plan.spl` and the selected `llm_caret_agent_teams` requirements provide provider-neutral launch and team-message plans. | Reuse launch-plan inputs; do not add room persistence to plans. |
| Runtime | `agent_runtime.spl` spawns Claude, Codex, and OpenCode and tracks only PID/status. Gemini, durable sessions, supervision, and injection are absent. | Put lifecycle operations behind `AgentControlPort`; process spawning is one adapter. |
| Provider dispatch | `provider.spl` is a closed model-backend registry and has no Codex/Gemini provider entries. | Keep chat transports and agent control out of provider dispatch. |
| Chat/session seam | `chat_tui.spl` injects `SessionHooks`, keeping command parsing testable and avoiding cycles. | Mirror this with `MessagingHooks` and explicit ports. |
| Server | `server.spl` builds OpenAI/Anthropic-compatible completion responses; `main.spl` already contains request-size, bearer-auth, and rate-limit hardening. | Build a dedicated messaging server and reuse security patterns, not routes/types. |
| Web infrastructure | `app.ui.web` has origin/token-gated WebSocket handling and bounded channels. | Reuse common infrastructure patterns without importing the UI server into the domain. |
| Discovery | `agent_discovery.spl` extracts names from small MCP/plugin manifests with string scanning. | Replace for this lane with a typed, versioned integration manifest decoded by repository SDN utilities. |
| Generic plugins | `app.plugin.registry` models SFFI libraries, functions, and classes and has some bespoke top-level entry splitting around the real SDN decoder. | Keep it for native transport SDK libraries; create an integration manifest for hooks, MCP, skills, migrations, and settings ownership. |
| Prior lane | `doc/01_research/*/llm_caret_agent_teams.md` and its requirements explicitly defer persistent teams, live discovery, supervision, and message transport. | Do not overwrite or silently broaden that completed slice. Link it as predecessor evidence. |

## Dependency boundary

The target dependency direction is:

`domain <- ports <- application <- adapters <- composition`

The domain owns canonical identities, rooms, messages, receipts, tasks, artifacts, profiles, policies, and capabilities. It must not import Claude, Codex, Gemini, Slack, Teams, or another adapter type. External transports normalize events; they never invoke agents directly. Agent adapters consume a deterministic `ContextBundle`; they never own room truth.

## Repository risks

- Adding messaging branches to `provider.spl` would conflate model inference with chat delivery and create a second extension-axis bottleneck.
- Expanding `AgentTeamMailbox` would break its pure immutable test role while still lacking persistence and identity semantics.
- Extending the compatibility completion server would mix provider protocol and room APIs.
- Reusing the SFFI manifest for integration ownership would make safe settings merge/uninstall and migrations unverifiable.
- Module-level LLM state must be isolated behind instance-scoped services before multiple rooms or agent sessions share a process.
- Production wrappers must execute cached compiled artifacts; synchronous hooks must enqueue locally and return promptly.

## Required follow-up inspection before design freeze

1. Map the actual SDN schema/decoder APIs suitable for a versioned integration manifest.
2. Use `std.database.pure_sql.PureDatabase`, the repository's SQLite-compatible engine rewritten in Simple, with event-store migration conventions.
3. Identify reusable HTTP/SSE/WS primitives without coupling to `app.ui.web` composition.
4. Trace current session persistence and all module-level mutable state in `llm_caret/mod.spl` and `main.spl`.
5. Measure current LLM Caret and MCP startup/latency/RSS baselines before setting final NFR targets.

## Conclusion

Create `src/app/llm_caret/messaging/` as a peer of provider and team-planning code. Preserve existing public compatibility surfaces and integrate only through composition and adapters.
