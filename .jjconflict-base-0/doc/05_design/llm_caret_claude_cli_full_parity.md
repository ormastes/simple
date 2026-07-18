# LLM Caret Claude CLI Full Parity - Detail Design

Date: 2026-07-05
Updated: 2026-07-07 (current-state reset + production-quality design)

## Current State (verified 2026-07-07)

This doc previously described an 8-phase "full parity" program keyed to file/LOC/
symbol matrices and a size-parity gate. A source audit (see
`doc/09_report/llm_caret_claude_cli_traceability.md` scope note and the
2026-07-07 gap analysis) shows that framing does not match the code. The
honest state is two separate trees:

### Shipped core (runs in the CLI)

- Root of `src/app/llm_caret/` — 13 files, ~3,086 LOC.
- Live path: `mod.spl` -> `provider.spl` (`dispatch_send`) -> one of
  `claude_api.spl`, `claude_cli.spl`, `openai_api.spl`, `openai_compat.spl`,
  `opencode_cli.spl`. Config via `config.spl`, transport helpers in
  `json_helpers.spl`, HTTP surface in `server.spl`, chat history in `chat.spl`.
- This is a provider/wrapper client. Its strongest dimension is streaming
  (`claude_cli.spl`: `CliStreamEvent`, `parse_claude_stream_line`,
  `claude_cli_stream`). Config loading (`load_config`, `parse_config_text`) is
  real.

### `claude_full/` island (does NOT run)

- ~720 files, ~151K LOC under `src/app/llm_caret/claude_full/`.
- `grep -rn "claude_full" src/app/llm_caret/mod.spl provider.spl config.spl`
  returns **zero matches**. Nothing outside `claude_full/` references it, and it
  has no `fn main`. It is an unreachable island.
- Much of it is data-model scaffolding or stubs: 18 of 21 `tools/*` dirs are
  1-2 line name-constant stubs (`tools/BashTool/toolName.spl` is a `BASH_TOOL_NAME`
  const + getter). `FileReadTool.spl` (1183 LOC) states in its own docstring it
  "models the source FileReadTool contract with deterministic data objects...
  without filesystem or SDK calls" — it never touches the FS.
- ~1,290 `parity-ledger` comment lines (in `commands/ultraplan.spl`,
  `commands/terminalSetup/terminalSetup.spl`, and one more) are LOC padding
  toward the retired size-parity gate, not behavior.

### Consequence

The prior "P7: Integration Shell / wire claude_full behind a provider flag"
never happened. Treat `claude_full/` as a **parts bin**, not a shipping
subsystem. Every capability below is designed against the **shipped path**; for
each we state which `claude_full` modules to WIRE IN, REWRITE, or DELETE.

---

## Production-Quality Design vs Claude Code

Each dimension: target architecture in the shipped path, disposition of existing
`claude_full` modules, and acceptance criteria. Severities carried from the
2026-07-07 gap analysis.

### 1. Session / compaction / resume  (P0)

- **Target:** Add summarizing compaction to `chat.spl`. When history nears the
  token budget, summarize the oldest span via one model call and replace it with
  a summary message, preserving a recent-message tail. Persist history as JSONL
  after every turn (use the existing `config_history_file` knob) and add a
  `--resume <session-id>` load path in `claude_cli.spl`/`provider.spl`.
- **claude_full disposition:** WIRE IN the data model and boundary logic from
  `commands/compact/compact.spl` (`CompactContext`, `CompactCallResult`,
  `messagesAfterBoundary`, `postCompactionMarked`) and paging from
  `assistant/sessionHistory.spl` (`HistoryPage`, `SessionEventsResponse`).
  DELETE the TUI-only compact UI.
- **Acceptance:** it-block test proves (a) a >budget history is compacted to a
  summary+tail and the summary call is issued, (b) truncation is no longer the
  only strategy, (c) `--resume <id>` reconstructs history from the JSONL file.

### 2. Tool execution + permission gating  (P0)

- **Target:** A real tool-dispatch layer in the shipped path: a `run_tool(name,
  input)` that (1) routes to a real executor — process spawn for Bash, real FS
  calls for read/write/edit, real fetch for WebFetch — and (2) passes every call
  through a single `permission_gate(mode, tool, input)` returning
  allow/ask/deny BEFORE execution. `deny` must block; `ask` must be answerable.
- **claude_full disposition:** WIRE IN the permission protocol structs from
  `bridge/bridgePermissionCallbacks.spl` (`BridgePermissionRequest`,
  `PermissionUpdate`, `BridgePermissionResponse`) as the gate's data model.
  REWRITE all `tools/*` name-constant stubs into real executors (or implement
  executors fresh in the shipped tree and keep only the tool-name registry).
  REWRITE `FileReadTool.spl` to actually read the FS. DELETE tool dirs with no
  shipping need.
- **Acceptance:** it-block test proves a denied Bash call does NOT spawn a
  process (assert on a spawn spy, not on a struct field), an allowed call does,
  and `ask` routes to the responder. No tool executes without traversing the
  gate.

### 3. Retry / backoff / timeout  (P0)

- **Target:** A `with_retry(fn)` wrapper around `dispatch_send` in `provider.spl`
  with bounded exponential backoff on 429/5xx/transient network errors, a
  retryable-vs-terminal error distinction, and a per-attempt timeout on every
  `rt_http_request` and `rt_process_run` call site.
- **claude_full disposition:** none reusable — implement fresh in the shipped
  tree.
- **Acceptance:** it-block tests for both branches: a mock 429-then-200 succeeds
  after backoff (assert attempt count), a mock persistent-500 exhausts retries
  and surfaces a terminal error; a hung subprocess is killed at the timeout.

### 4. Streaming  (P2 — already the strongest)

- **Target:** Keep `claude_cli.spl` streaming. Add buffer-boundary robustness so
  a JSON event split across two process-output chunks is reassembled.
- **claude_full disposition:** none needed.
- **Acceptance:** it-block test feeds a `CliStreamEvent` JSON line split across
  chunk boundaries and asserts a single correct event is parsed.

### 5. MCP client  (P1)

- **Target:** A real MCP **client** module in the shipped path: stdio transport
  first (SSE/HTTP later), `.mcp.json` config load, `initialize` handshake,
  `tools/list`, `tools/call`. Discovered tools register into the tool-dispatch
  layer (dimension 2) and pass the same permission gate.
- **claude_full disposition:** `utils/mcpWebSocketTransport.spl` and
  `components/mcp/*` are UI-only with no protocol client — DELETE or ignore;
  build the client fresh. Note: `server.spl` in the shipped tree is an MCP-like
  *server* surface, not a client — leave it as is.
- **Acceptance:** fake-transport it-block test drives handshake -> list -> call
  and asserts a discovered tool is invocable through the gate; one opt-in,
  credential-gated live-server system test.

### 6. Subagents  (P1)

- **Target:** A minimal `Task` runtime: spawn a subagent with its own message
  history and tool-permission subset, run its own tool-use loop to completion,
  return a synthesized result to the parent loop. Single-subagent first;
  parallel fan-out later.
- **claude_full disposition:** none reusable — `agents/*` components edit config
  files, and `TaskCreateTool`/`TaskGetTool`/etc. are 1-line stubs. Implement
  fresh. If not implemented this cycle, explicitly DESCOPE from the parity claim
  in docs rather than implying coverage.
- **Acceptance:** it-block test spawns one subagent that runs a gated tool and
  returns a result string to the parent; parent history contains the synthesized
  result.

### 7. Prompt caching  (P1)

- **Target:** Insert `cache_control` breakpoints into
  `build_claude_api_body` (`claude_api.spl`) for the system prompt and the
  static tool-definition block, so multi-turn sessions reuse cached prefixes.
- **claude_full disposition:** `CompactCallResult.promptCacheBreakNotified` is a
  data field only — ignore; implement body insertion fresh.
- **Acceptance:** it-block test asserts the built JSON body contains
  `cache_control` breakpoint markers on the system prompt and tool block.

### 8. Secret redaction + injection defense  (P0)

- **Target:** A redaction pass applied before ANY logging or history/JSONL
  persistence of request/response bodies — strip `Authorization` headers and
  API-key patterns (`sk-`, `claude_full` `workSecret`-style tokens). Add a basic
  prompt-injection mitigation: tag/wrap untrusted tool output (WebFetch, file
  content) before it re-enters message history.
- **claude_full disposition:** `bridge/workSecret.spl` and
  `AssistantRedactedThinkingMessage.spl` are island-only — reuse the redaction
  *patterns* if useful; implement the pass fresh in the shipped path around
  `provider.spl`/`chat.spl` persistence.
- **Acceptance:** it-block test proves a persisted transcript contains no raw API
  key, and that WebFetch output is wrapped/tagged before entering history.

### 9. Crash resilience / resume  (P1)

- **Target:** Timeout every `rt_process_run` call site (shared with dimension 3),
  persist chat history to disk on every turn (shared with dimension 1) so a
  crash loses at most the in-flight turn, and add a top-level error boundary that
  writes a recovery marker so `--resume` can continue.
- **claude_full disposition:** none reusable.
- **Acceptance:** it-block test kills a session mid-turn (simulated) and proves
  `--resume` reconstructs all completed turns from the JSONL file.

### 10. Observability  (P1)

- **Target:** Structured JSON-lines event emission around `dispatch_send`:
  per-request latency, error class, retry decisions, token/cost accounting.
  Satisfies NFR-LLM-CARET-FULL-004. Surface token/cost to a `/cost`-style
  command.
- **claude_full disposition:** no telemetry module exists in either tree —
  implement fresh.
- **Acceptance:** it-block test asserts one dispatch emits a structured event
  with latency, outcome, retry count, and token/cost fields.

### 11. UI — Simple TUI  (P1)  [updated 2026-07-07, user directive]

- **Directive:** the interactive UI uses Simple's own **pure-Simple** TUI
  framework (`std.tui`, ANSI-based, no ncurses / no FFI terminal lib) in most
  cases — not raw `print`, not a GUI, not a third-party dep. Prefer pure-Simple
  infrastructure wherever a stdlib module already covers the need.
- **Target:** A `chat_tui.spl` chat shell built on `std.tui` widgets
  (`BoxWidget` transcript panel, `ListWidget` scrollback, `InputWidget` prompt
  line, `TextWidget`/`style.*` for user-vs-assistant styling), following the
  proven render-loop pattern in `src/app/editor/tui_shell.spl`. The existing raw
  `print` at `chat.spl:172` (`_emit_tool`) is replaced by a `render_tool_call`
  widget line through a renderer seam on `run_agent_loop`.
- **"In most cases" nuance:** TUI is the default for an interactive TTY; when
  stdout is not a tty (piped / CI / MCP-server mode) the renderer seam falls back
  to the plain `print` path, so headless/JSON usage is unchanged.
- **claude_full disposition:** the island's `ink/`, `screens/`, `components/` UI
  is a React/Ink-style port that does NOT run and is NOT pure-Simple-TUI —
  ignore; build on `std.tui` fresh.
- **Acceptance:** it-block tests assert the pure formatting helpers (turn line,
  tool-call line, user-vs-assistant style) produce the expected strings, and that
  the renderer seam selects TUI vs plain correctly given a tty/flag input.
- **Known gap:** no incremental/streaming re-render in `std.tui` yet — assistant
  replies render after completion; streaming token render is the upgrade path.

---

## Design Principles

- All FS/process/network access goes through owner facades per MDSOC+ — no raw
  runtime shortcuts added to the shipped path.
- No size-parity gate. LOC is not evidence. A capability is done only when an
  executed it-block asserts the behavior (see quality gate in the impl plan).
- `claude_full/` is a parts bin: each module is either wired in, rewritten, or
  deleted per the dispositions above — it is not shipped wholesale and its LOC is
  not counted as parity.
- **Pure-Simple infrastructure first.** Reach for a Simple stdlib module before
  any FFI/C/Rust or external dependency (UI → `std.tui`; JSON → `json_helpers`;
  process/fs/net → owner facades). Drop to `extern`/runtime only when no
  pure-Simple path exists, and record why.
