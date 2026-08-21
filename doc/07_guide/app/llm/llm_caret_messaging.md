# LLM Caret Messaging Guide

## Purpose

LLM Caret messaging connects human rooms and agent sessions without treating chat platforms as model providers. The primitive Simple room is canonical; external transports advertise capability truth and may bind a primitive shadow room for missing behavior.

## Surface map

- `simple caret messaging serve`: primitive durable room server.
- `simple caret messaging mcp`: live agent-facing room/task tools.
- `simple caret messaging plugin install|check|uninstall`: managed Claude, Codex, and Gemini integration.

`caret` is a registered pure-Simple root command. A repository binary built
before that registration must be redeployed before it can expose the command.
The `bin/caret` production launcher intentionally requires a cached native
Caret artifact; source interpretation is an explicit diagnostic fallback only.

The direct launcher routes messaging commands through the minimal
`src/app/llm_caret/messaging/main.spl` control plane. It does not load the
legacy Caret UI/provider graph. Database-bearing actions still require their
fresh compiled carrier, including when this supervisor is interpreted.
- Messaging skills: usage/safety guidance for each agent surface.
- SPipe: requirements, executable scenarios, generated operator manuals, traceability, and release evidence. The existing SPipe MCP remains separate from live messaging.

## Semantic rules

Direct messages are private rooms. Transport receipt, human-read evidence, agent consumption, and task handling are distinct. A local cursor is never labeled native read. Agent progress does not trigger agents by default. Deterministic routing precedes any selector. Context is bounded, redacted, ACL checked, and recorded by IDs/hashes.

## Embedded storage

The primitive server uses Simple's SQLite-compatible engine rewritten in
Simple: `std.database.pure_sql.PureDatabase`. It does not use `sqlite_sffi` and
does not require the C SQLite library or an external database service. The
configured database path is durable, while `:memory:` is reserved for bounded
tests and ephemeral development. Room sequences, idempotency keys, cursors,
outbox entries, dead letters, audit events, and context manifests share the
same transactional store.

Normal operation uses the cached native database worker at
`build/database/llm_caret_messaging_db`, including when `caret` itself is
interpreter-hosted. `caret messaging database --probe` rebuilds the worker when
its source or PureDatabase adapter is newer, then executes the compiled worker.
The normal `caret messaging serve` command follows the same rule: it builds or
reuses `build/database/llm_caret_messaging_server` and supervises that process.
The HTTP server and PureDatabase hot path therefore never fall back merely
because the launching CLI happens to be interpreted.

The provider-neutral agent runtime resolves Claude Code, Codex, Gemini CLI,
Kimi CLI, and the retained OpenCode compatibility path. New callers that need
all explicit paths use the `*_with_all` entrypoints; `*_with_gemini` and the
older three-path entrypoints remain source-compatible. Kimi agent launch is
available at this runtime boundary; the managed messaging-plugin installer is
still the Claude/Codex/Gemini composite and must not claim Kimi hook support.

Use `launch_messaging_agent_plan` for a room task. It starts the selected
provider with only `LLM_CARET_TASK_ID`, `LLM_CARET_ROOM_ID`,
`LLM_CARET_AGENT_ID`, and the PureDatabase path added to its inherited process
environment. Managed hooks use those identifiers to correlate lifecycle
events; external transport credentials are never added to the agent process.
Use `--smf` only on a compiler that can lower the complete PureDatabase closure;
direct source interpretation is reserved for explicit diagnostics.

The MCP command uses the stronger whole-service boundary:
`simple caret messaging mcp` freshness-builds
`build/database/llm_caret_messaging_mcp` from `messaging/mcp_worker.spl` and
then runs it with inherited stdin/stdout. MCP framing, authorization, messaging
application logic, and PureDatabase therefore share the compiled worker. The
launcher may itself be interpreted without moving database work back into the
interpreter.

## Capability fallback

Adapters report `native`, `emulated`, `primitive_sidecar`, or `unsupported`. Application services select behavior from this record, never from a platform name. Public fallback notifications contain no private body.

`adapter/chat/primitive.spl` is the authoritative `ChatTransportPort`
implementation. It binds canonical room IDs, persists idempotent sends, returns
ordered history, advances explicitly local read cursors, and creates ACL-backed
direct rooms. `BoundChatTransport` remains the shared external-adapter contract
simulator and is not live-platform evidence.

The first external adapter cores live in `adapter/chat/matrix.spl` and
`adapter/chat/slack.spl`. They maintain canonical-to-external room bindings,
construct authenticated native send requests, preserve native thread IDs,
deduplicate normalized inbound event IDs, and report receipt behavior honestly:
Matrix exposes its native receipt operation, while Slack advances the primitive
sidecar cursor rather than claiming a human-native read receipt. These contract
tests prove request/normalization semantics only; credential-backed gates are
still required before either platform is marked live.

Teams and Telegram follow the same boundary. The Teams adapter sends through
an already-installed Bot Framework conversation and can preserve a native
reply activity ID; it does not claim that a bot can freely create tenant rooms
or prove channel reads. The Telegram adapter sends only to an existing chat;
it uses a native reply parameter when the canonical message has an external
mapping and otherwise renders a content-safe canonical reply reference. It
does not claim arbitrary bot-initiated private conversations or human-read
receipts. Missing features use the bound primitive room.

Canonical transport bindings and external message/thread references are stored
in PureDatabase. This lets a restarted bridge recover the external room,
capability snapshot version, mirror policy, cursors, and canonical-to-remote
message mapping instead of relying on adapter-process memory.

Google Chat, Discord, and Mattermost also have concrete request cores. Google
Chat preserves bound spaces and thread names. Discord emits native message
references but keeps read evidence in the primitive room. Mattermost emits
channel posts with root IDs and supports direct-channel creation intent. These
are contract-tested adapter cores; they are not credential-backed live PASSes.

LINE and KakaoTalk expose only their genuine narrow subsets. LINE sends to an
already-bound user/group and can attach a quote token. KakaoTalk sends only to
the authenticated account or an explicitly authorized friend. Primitive rooms
provide creation, private-room ACLs, threads, profiles, and canonical read
state; neither adapter is advertised as a complete external room backend.

## Installation safety

The plugin merges existing settings, backs up changed files, records ownership and hashes, verifies hook executables and MCP discovery, and removes only still-owned entries. Hook files refer to scoped local capabilities and credential references; they contain no external transport secrets.

Configuration is decoded with the repository SDN parser. Quote URI-like SDN
scalars, for example `"unix://..."` and `"secret://slack/workspace"`, because
an unquoted colon denotes SDN structure. Run
`simple caret messaging config check --config=PATH` before starting a bridge.
External credentials resolve only inside the bridge process through a derived
`SIMPLE_SECRET_*` capability name; secret values are never written to config,
hooks, argv, audit output, or PureDatabase.

The composite plugin packages the shared messaging skill and an MCP launch
environment containing only the database path, canonical local identity,
workspace, and scopes. The MCP server binds authorization to those process
values. Supplying another identity or workspace inside a tool call cannot grant
access. `chat_get_context` persists its context manifest, and MCP rooms,
memberships, profiles, tasks, artifacts, and idempotency records survive server
restart in PureDatabase.

## Evidence

Simulator contract tests prove normalization, fallback, deduplication, and retry classification only. Live platform status requires credential-backed evidence. Unavailable platform rows remain visibly blocked or unsupported.
The v1 installer treats Claude, Codex, and Gemini as one composite activation.
`--agents claude,codex,gemini` is validated rather than ignored; partial and
unknown selections fail before writes. The selected-agent SDN record is covered
by the same backup, hash, drift-check, and guarded-uninstall policy as the rest
of the bundle.
## Bounded multi-Caret launch

`app.llm_caret.multi_caret_manager` launches a finite Claude, Codex, Gemini,
Kimi, or OpenCode batch behind one parent-owned lifecycle. Set an explicit
capacity (maximum 16); over-capacity requests fail before spawn, and partial
launches are rolled back. The returned terminal embed is a display-only pane
model, not an `os.apps.smux` session. Call the manager poll and stop operations
rather than acting on child PIDs.
