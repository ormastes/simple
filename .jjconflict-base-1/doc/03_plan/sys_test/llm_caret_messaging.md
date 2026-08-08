# LLM Caret Messaging — System Test Plan

## Scope

Modern step-based SSpec exercises real production domain/application surfaces first, then the real primitive pure-Simple `PureDatabase`/server/hook/MCP vertical slice. Live transport tests are independent credential gates.

## Manual flow

Visible steps are `Enroll a primitive account`, `Create and bind a room`, `Route a message to an agent`, `Inject the bounded context bundle`, `Observe task and receipt transitions`, and `Recover messaging state after restart`. Setup is folded/inline; matrices and external platform details are folded. Protocol/log/artifact captures are linked, with concise API/TUI evidence embedded.

## Traceability

| Requirements | Executable evidence | Coverage |
|---|---|---|
| 001–003, 012, 015–016 | `llm_caret_messaging_primitive_spec.spl`, `llm_caret_messaging_http_application_spec.spl` | Enrollment, rooms, PureDatabase/history/cursors/direct rooms/restart/HTTP/SSE |
| 006–008, 014 | `llm_caret_messaging_agent_control_spec.spl` | Claude/Codex/Gemini attach, context, task control, lifecycle normalization |
| 004–011, 014 | `llm_caret_messaging_domain_spec.spl` | Naming, commands, routing, context, profiles, updates, notify, loops |
| 013 | `llm_caret_messaging_mcp_spec.spl`, focused installer/agent specs | Plugin install/check/uninstall, skills, MCP handshake/tools, hook queue/bridge |
| 017 | `chat_transport_contract_spec.spl`, `transport_capability_spec.spl` | Capability truth/fallback plus shared adapter contract; live gates remain separate |

Each REQ receives happy, edge, and error cases across the suite. Generated manuals mirror these paths under `doc/06_spec/03_system/app/llm_caret/feature/` and must report zero stubs.

## Gates

Run focused unit specs, the four system specs, docgen/manual review, lint, duplication, direct-env guards, layout guard, performance fixture, and credential-backed platform rows. Missing live credentials remain explicit blocked evidence, not PASS.
## Durable provider lifecycle correlation

- Normalize Claude, Codex, and Gemini lifecycle events.
- Correlate hook events to canonical task, room, and agent IDs.
- Assert task-event history, milestone/terminal room updates, and handled
  receipts without allowing `agent_update` to trigger another task.
