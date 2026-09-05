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
## Phase 3/4 CLI verification

`test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl`
keeps the compiler/product boundary fail-closed. Phase 3 must identify as
`simple-bootstrap` and reject `run`, `test`, and `caret`. The exact admitted
Phase 4 binary must run source, execute a real SSpec assertion, expose
`caret messaging`, and report every compiled carrier provenance-ready.

Run with retained noncanonical artifacts as:

```bash
SIMPLE_STAGE3_BINARY=/absolute/path/to/stage3/simple \
SIMPLE_STAGE4_BINARY=/absolute/path/to/full/simple \
/absolute/path/to/full/simple test \
  test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl \
  --mode=interpreter --clean --fail-fast
```

The canonical admission wrapper retains the binary identities, negative Phase
3 boundary outputs, Phase 4 system-test transcript, and final result receipt:

```bash
sh scripts/check/check-llm-caret-phase4-cli-admission.shs \
  /absolute/path/to/stage3/simple /absolute/path/to/full/simple
```

This gate is intentionally RED while TODO 681 is blocked. A Phase 3
`native-build` success, source inspection, Rust seed, stale full CLI, or carrier
files without matching provenance cannot satisfy it.

The 2026-08-10 recovery attempt ended with status 143 during Phase 4 HIR
lowering after 1,474 cache objects and produced no executable. That attempt is
diagnostic evidence only; resume from the preserved cache before invoking the
admission wrapper.

| Requirement | Executable system coverage | Evidence |
|---|---|---|
| REQ-LLM-MSG-013 | Phase 3 rejects product commands; Phase 4 runs source/tests and exposes Caret Messaging help | Exact binary paths, SHA-256, stdout/stderr, exit codes |
| REQ-LLM-MSG-016 | Phase 4 reports database/MCP/hook/bridge/server ready | Fresh carrier artifacts and matching provenance records |
