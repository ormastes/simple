# LLM Caret — Usage Guide

Date: 2026-07-07

Production-quality features of the shipped `src/app/llm_caret` path. Pure-Simple;
UI on the Simple TUI stdlib (`std.tui`).

## Interactive chat UI (Simple TUI)

The chat runs on Simple's own `std.tui` framework (ANSI, no ncurses/FFI):
a scrollable transcript panel, a prompt input line, and styled user/assistant
turns. Entry point: `caret_chat(ui, policy, responder, ui_mode)` in
`chat_tui.spl`.

`ui_mode` selects the renderer — **Simple TUI in most cases**:

| `ui_mode` | Behavior |
|-----------|----------|
| `"auto"` (default) | Full-screen TUI on an interactive terminal; plain print when non-tty |
| `"tui"` | Always the full-screen TUI |
| `"plain"` | Always plain line output (pipes / CI / server) |

`"auto"` probes `$TERM` (no `isatty` extern exists in the stdlib). `$TERM` is
inherited even under a pipe, so **pass an explicit `ui_mode` ("plain"/"tui")
in CI and servers**. In-TUI keys: `Enter` sends, `/exit` or `/quit` leaves,
`Ctrl-C`/`Ctrl-D` aborts.

Assistant replies render after completion (non-streaming); `std.tui` has no
incremental re-render yet — that is the documented upgrade path.

## Retry / backoff / timeout

Every provider HTTP call is wrapped in `with_retry` (`retry.spl`): retries on
429 / 5xx / connection errors with exponential backoff + jitter, honors
`Retry-After`, and applies a per-request timeout. Non-retryable 4xx fail fast.

- `LLM_CARET_MAX_RETRIES` — override max attempts (default 4). A hung subprocess
  is killed at the timeout rather than waited on indefinitely.

## Tool execution + permission gating

Tools (`tools.spl`) run through a single `PermissionPolicy` gate — nothing
executes ungated:

- Read-only tools (`read_file`, `list_dir`, `glob`) are auto-allowed.
- `bash` and `write_file` require an explicit grant (config `tools.allow` list
  or an allow-all flag). Un-granted, non-interactive calls return a
  permission-denied `tool_result` to the model — they do **not** execute.
- File tools are path-guarded to the workspace root (`..` traversal rejected).
- `bash` output is truncated (~30 KB); the agent loop is capped at 25 iterations.

## Secret redaction + injection defense

`redact.spl` masks secrets (`sk-ant-*`, `sk-*`, `ghp_*`/`github_pat_*`, `AKIA*`,
`Bearer` tokens, `*_API_KEY=`/`*_TOKEN=` assignments, PEM blocks — last 4 chars
kept) before any log / error / echo in `claude_cli.spl` and `server.spl`. The
live outbound `Authorization` header is never redacted (requests still work) —
only displayed/logged copies. `wrap_untrusted(source, content)` fences external
/ tool output with a do-not-follow-instructions notice before it re-enters
history.

## Response parsing note

JSON extraction uses `json_helpers.json_find` + `json_parse_int` (boxing-free),
not `text.index_of`/`int()`/`char.to_i64()` — the seed mis-boxes `Option<i64>`
and cross-module `char.to_i64()`. See
`doc/08_tracking/bug/llm_caret_index_of_optioni64_tagbox_2026-07-07.md`.

## Related

- Design: `doc/05_design/llm_caret_claude_cli_full_parity.md`
- Plan: `doc/03_plan/agent_tasks/llm_caret_claude_cli_full_parity_impl_plan.md`
- Trace gate (docs-coverage only): `llm_caret_claude_cli_harden.md`
