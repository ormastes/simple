# LLM Caret — Usage Guide

Date: 2026-07-07 (last revised 2026-08-25)

Production-quality features of the shipped `src/app/llm_caret` path. Pure-Simple;
UI on the Simple TUI stdlib (`std.tui`).

## GUI backends

LLM Caret keeps the same provider and `/api/chat` contract across its GUI
surfaces:

- `--gui` serves the browser GUI and opens the system browser.
- `--electron` serves that GUI and opens it in the canonical repository
  Electron shell. For local automation only, set
  `LLM_CARET_ELECTRON_DEBUG_PORT` to expose Electron's debugging endpoint.
- `--metal-gui` runs the pure-Simple native GUI. Semantic HTML is parsed and
  laid out by Simple Web into `DrawIrComposition`; Engine2D then owns Metal
  lowering and presentation. The path fails closed unless readback reports
  `device_readback`, a positive backend handle/device identity, the expected
  pixel count, and a nonzero checksum.

The native composer accepts keyboard input, Enter submission, and Send-button
clicks. With the deterministic test provider, submitting `test` displays
`hello`. Use `--provider dummy` for that smoke test; the Metal GUI intentionally
rejects other providers until an asynchronous provider bridge is designed.

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

## Agent workspaces + the `workspace` dev CLI

Each agent gets one **detached git worktree** (`git worktree add --detach`,
never a branch) plus one tmux window, on a **private tmux socket**
(`tmux -L caret_ws_<id>`) so the operator's own tmux server is never touched.
Implementation: `src/app/llm_caret/agent_workspace.spl` (side effects) over the
model-only `agent_tmux.spl` embed; CLI in `workspace_cli.spl`.

```sh
bin/simple run src/app/llm_caret/main.spl workspace <id> <cmd> [args] \
    [--repo <path>] [--root <path>]
```

`--repo` defaults to the cwd; `--root` defaults to
`<repo>/build/caret_worktrees/<id>` (gitignored). Worktree paths are resolved
absolute — `git -C <repo>` would otherwise resolve a relative path against the
repo, not the cwd.

| command | effect |
|---|---|
| `status` | socket, session name, alive flag, worktrees, panes |
| `attach <agent> [cmd]` | detached worktree + tmux window for `<agent>`; prints both |
| `detach <agent>` | kill the window and remove the worktree |
| `add <agent>` / `remove <agent>` | worktree only, no tmux |
| `list` | worktrees git knows about for `--repo` |
| `panes` | every pane target in the session |
| `send <target> <cmd...>` | `send-keys` to one pane |
| `broadcast <cmd...>` | `send-keys` to **every** pane |
| `capture <target>` | print a pane's scrollback |
| `wait <target> <marker> [ms]` | block until `<marker>` appears (default 30000 ms) |
| `suite <spec> [wait_ms]` | run `bin/simple test <spec>` in a `caret_suite` window; with `wait_ms`, poll for the authoritative `Results:` line and echo the verdict |
| `kill` | kill the private tmux server |

Exit codes: **0** ok, **1** the command ran and failed (including
`tmux_unavailable`, `no_panes`, a `wait`/`suite` timeout), **2** usage —
which includes a bare `workspace <id>`, `workspace <id> help`, an unknown
command, and a command missing its required positional. `add`, `remove` and
`list` are the only commands that work without tmux installed.

**Recursion protection.** Every command the workspace spawns is prefixed
`LLM_CARET_WORKSPACE_DEPTH=<n+1>`. `launch_caret_suite` refuses with
`recursion_limit` once the depth is at `MAX_DEPTH` (currently **1**), so a
suite launched inside a workspace cannot launch another. Independently,
`send_to_each_pane` skips the pane the process itself is running in (read from
`TMUX_PANE`), so a broadcast never feeds itself. The same idea is implemented
for shell scripts by `scripts/lib/recursion_guard.shs` — see
`doc/07_guide/tooling/build_fast_path.md`.

Evidence: `test/01_unit/app/llm_caret/agent_workspace_spec.spl` (throwaway
`git init` fixture, two-pane broadcast with a per-pane marker oracle),
`test/03_system/app/llm_caret/workspace_cli_system_spec.spl` (real CLI child
processes: 3-agent team, worktree isolation, broadcast, nested-suite refusal),
`agent_team_workspace_system_spec.spl`, `workspace_recovery_system_spec.spl`,
`workspace_embed_parity_system_spec.spl` and
`caret_suite_tmux_window_system_spec.spl` (a real suite run inside a tmux
window). With tmux absent these report `pending("BLOCKED: ...")`, never a
silent pass.

## Tool execution + permission gating

Tools (`tools.spl`) run through a single `PermissionPolicy` gate — nothing
executes ungated:

- Read-only tools (`read_file`, `list_dir`, `glob`) are auto-allowed.
- `bash` and `write_file` require an explicit grant (config `tools.allow` list
  or an allow-all flag). Un-granted, non-interactive calls return a
  permission-denied `tool_result` to the model — they do **not** execute.
- File tools are path-guarded to the workspace root (`..` traversal rejected).
- `bash` output is truncated (~30 KB); the agent loop is capped at 25 iterations.

## Infrastructure tools (mail + file server)

Caret reaches infrastructure servers through first-class tools, never by
shelling out to `curl`/`mc`. Server-facing code lives in
`src/app/llm_caret/infra_mail.spl` and `infra_storage.spl`; `tools.spl` only
adds the schema entries, dispatch arms and permission classification.
`tool_schemas()` returns every entry (Anthropic `name`/`description`/
`input_schema` shape) for providers to hand to the model.

| Tool | Arguments | Class | Backing facade |
|------|-----------|-------|----------------|
| `mail_list` | `mailbox` (default INBOX), `limit` (<=200) | read-only | IMAP `SELECT` + `FETCH` headers via the RFC 3501 parser in `std.nogc_sync_mut.imap.parse` |
| `mail_read` | `uid` | read-only | IMAP `UID FETCH (BODY.PEEK[])` (`imap_build_uid_fetch`), literal-aware body extraction |
| `mail_send` | `to`, `subject`, `body` | **mutating** | SMTP `EHLO`/`AUTH PLAIN`/`DATA`, `std.nogc_sync_mut.smtp` |
| `storage_ls` | `bucket`, `prefix` | read-only | `app.devhub.adapter_minio` (pure-Simple SigV4, same path as `bin/itf minio ls`) |
| `storage_get` | `key`, `bucket`, `max_bytes` (<=262144) | read-only | SigV4 ranged GET |
| `storage_put` | `key`, `content` (<=4 MiB), `bucket` | **mutating** | SigV4 PUT |

Permission behaviour is identical to the workspace tools: the four read-only
tools are auto-allowed; `mail_send` and `storage_put` go through the same
allow/deny gate as `bash`/`write_file` and are **denied by default** (config
`tools.allow` or the allow-all flag grants them). Every failure — denied,
unconfigured, bad argument, unreachable server — comes back as a tool error;
no arm aborts the process.

Config lives in `llm_caret.sdn`; credentials are **env references only**:

```
mail:
    imap_host: imap.example.com
    imap_port: 993           # 993 / 465 => implicit TLS; other ports plaintext
    smtp_host: smtp.example.com
    smtp_port: 465           # 587 (STARTTLS) is refused: no in-place TLS upgrade
    user: me@example.com
    secret_env: CARET_MAIL_SECRET

storage:
    backend: minio           # minio | ftp (ftp refused: rt_ftp_* unbacked)
    endpoint: minio.corp:9000
    bucket: caret
    access_key_env: CARET_S3_ACCESS_KEY
    secret_key_env: CARET_S3_SECRET_KEY
    tls: true                # URL scheme when endpoint has none
```

Missing sections give `mail not configured: set [mail] in llm_caret.sdn` /
`storage not configured: set [storage] in llm_caret.sdn`; an unset secret env
names the variable, never a value.

Mail hardening (2026-08-25):

- **IMAP responses are parsed, not line-scanned.** Framing and parsing are
  literal-aware (`imap_response_complete` / `imap_parse_fetch_response` in
  `std.nogc_sync_mut.imap.parse`): a message body containing `)`, CRLFs or a
  tag-looking line can no longer terminate a reply early or corrupt
  `mail_list` rows. Folded headers are unfolded; UTF-8 literals are consumed
  by byte count.
- **Every server read is bounded.** A server that accepts and then stalls
  fails the tool call with `mail server timed out after N ms` (default
  budget 15 s per reply; TLS reads use `tls_read_timeout`, plaintext reads
  the fd read-timeout) instead of hanging the caret turn.
- **STARTTLS (587/143) is negotiation-ready but refused** — the state machine
  ships in `app.llm_caret.infra_mail_starttls`, the transport does not. See
  Known limitations.

Specs:
`test/01_unit/app/llm_caret/infra_tools_spec.spl` (schemas, gating,
validation), `test/01_unit/lib/nogc_sync_mut/imap/fetch_parse_spec.spl`
(FETCH parser), `test/01_unit/app/llm_caret/infra_mail_starttls_spec.spl`
(STARTTLS transcripts), `test/01_unit/app/llm_caret/infra_mail_timeout_spec.spl`
(bounded reads) and `test/03_system/app/llm_caret/infra_servers_system_spec.spl`
(live round trips, gated on `LLM_CARET_MAIL_LIVE=1` / `LLM_CARET_STORAGE_LIVE=1`
+ `LLM_CARET_CONFIG`; no in-repo SMTP/IMAP/S3/FTP server exists, so they are
honestly blocked on a bare host).

## Wiki tools

`infra_wiki.spl` adds a wiki surface behind the same gate:

| Tool | Arguments | Class | Backing |
|------|-----------|-------|---------|
| `wiki_search` | `query` | read-only | one line per hit: `id<TAB>title<TAB>url` |
| `wiki_read` | `page_id` | read-only | `Title:` / `Id:` header lines, then the body |
| `wiki_write` | `page_id` (update) or `parent` + `title` (create), `body` | **mutating** | same allow/deny gate as `write_file` |

Two backends, selected by `[wiki] backend` in `llm_caret.sdn`:

- `confluence` — the existing devhub adapter (`app.devhub.adapter_confluence`,
  the `bin/itf wiki` code path). Auth is Basic `user:token`; the token is read
  **only** from the env var named by `token_env` (validated as a strict
  identifier), routed through ItfConfig's `token_cmd` seam so the devhub
  `auth.sdn` plaintext fallback is never consulted. `space` is required to
  create pages.
- `local` — a markdown directory; no server needed. `root` (default `doc`,
  resolved under the workspace root) holds the pages; a page id is the `.md`
  path relative to `root`. Search is a case-insensitive substring scan over
  `*.md` (path + body); write only ever writes under `root` and rejects `..`
  traversal and absolute paths outside it.

```
wiki:
    backend: local           # confluence | local
    root: doc                # local: markdown dir (relative to workspace root)
    base_url: https://x.atlassian.net/wiki   # confluence only
    space: ENG               # confluence space id (required to create)
    user: me@example.com     # confluence user
    token_env: CARET_CONFLUENCE_TOKEN        # env var holding the API token
```

Unconfigured use answers `wiki not configured: set [wiki] in llm_caret.sdn`;
an unsupported backend or a missing token names the problem and never aborts.
Specs: `test/01_unit/app/llm_caret/infra_wiki_spec.spl` (local round trip,
traversal, gating) and the `LLM_CARET_WIKI_LIVE=1`-gated Confluence row in
`infra_servers_system_spec.spl`.

## Using caret tools from Claude Code / Codex via MCP

The compiler MCP server (`bin/simple_mcp_server`, `src/app/mcp/main.spl`)
exposes all nine infra tools to any MCP client as `caret_*`:

`caret_mail_list`, `caret_mail_read`, `caret_mail_send`,
`caret_wiki_search`, `caret_wiki_read`, `caret_wiki_write`,
`caret_storage_ls`, `caret_storage_get`, `caret_storage_put`.

Semantics:

- **Confirm gate.** The mutating three (`caret_mail_send`, `caret_wiki_write`,
  `caret_storage_put`) are DENIED with an `isError` tool result unless the
  call passes `"confirm": true` in its arguments (each schema description says
  so). With it, the call is granted exactly that one tool; read-only tools
  need no confirm.
- **Process boundary.** The server never imports the caret/devhub/imap module
  graph (that was measured to double its startup); each `caret_*` call runs
  the one-shot CLI `simple run src/app/llm_caret/tool_cli.spl <tool>
  <input.json> [--allow]` as a child and returns its stdout. Handlers live in
  `src/app/mcp/main_lazy_caret_tools.spl`.
- **Config.** The server process reads `$LLM_CARET_CONFIG` (path to an
  `llm_caret.sdn`); unset, every call reports caret's honest "not configured"
  error. The workspace root for the local wiki and file guards is the server
  cwd.

`.mcp.json` snippet (Claude Code; Codex's `mcp_servers` block is analogous):

```json
{
  "mcpServers": {
    "simple-mcp": {
      "command": "bin/simple_mcp_server",
      "env": {
        "LLM_CARET_CONFIG": "/abs/path/llm_caret.sdn",
        "CARET_CONFLUENCE_TOKEN": "${CARET_CONFLUENCE_TOKEN}"
      }
    }
  }
}
```

The default `auto` tool set serves a small core list on the first
`tools/list`; the caret tools appear in the full list (`SIMPLE_MCP_TOOL_SET=all`
forces it immediately). End-to-end spec:
`test/03_system/app/mcp/caret_tools_mcp_system_spec.spl`.

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

## Known limitations

Every row here is a real, currently-open constraint — not a roadmap item.

| # | limitation | consequence | unblock condition |
|---|---|---|---|
| 1 | **No in-place TLS upgrade of a connected fd.** `rt_tls_client_from_fd` does not exist anywhere in the runtime. | `smtp_port: 587` / `imap_port: 143` are refused *before* connecting, with an error naming the missing symbol. The RFC 3207 / RFC 3501 negotiation state machine (`infra_mail_starttls.spl`) is implemented and transcript-proven, but has no transport. Use 465/993 (implicit TLS) or a plaintext port. | runtime lane backs `rt_tls_client_from_fd`; C-side design in `doc/08_tracking/bug/tls_no_fd_upgrade_blocks_starttls_2026-08-25.md` |
| 2 | **FTP storage backend is unbacked.** The `rt_ftp_*` externs have no runtime definition. | `backend: ftp` is refused with an explicit error; the FTP row of `infra_servers_system_spec.spl` stays BLOCKED. Only `backend: minio` works. | runtime lane backs `rt_ftp_*`, or a pure-Simple FTP client over `io.tcp` is requested |
| 3 | **Live infra evidence needs a Docker host.** | On a bare host `check-llm-caret-infra-live.shs` exits **2** with `ERROR`, and the `*_LIVE=1` rows of `infra_servers_system_spec.spl` are honestly skipped. There is no in-repo SMTP/IMAP/S3 server. | a CI runner with Docker |
| 4 | **Five caret specs are environment-blocked on a Stage 4 CLI**: `cli_cached`, `cli_hidden_cached`, `native_closure`, `tui_pty`, `messaging_phase_cli`. | They need a cached self-hosted caret artifact and `SIMPLE_STAGE3/4_BINARY`; today's binary cannot produce one, so they report BLOCKED rather than passing. | bootstrap redeploy reaching Stage 4; then rerun the caret census |
| 5 | **All caret evidence to date is on the Rust seed**, not a self-hosted binary. | A green caret suite is not proof of self-hosting. | same Stage 4 redeploy as row 4 |
| 6 | **The MCP `auto` tool set serves 3 core tools where specs pin 20** (pre-existing at origin). | The `caret_*` tools are reached via the full list; `SIMPLE_MCP_TOOL_SET=all` forces it immediately. | filed as `mcp_core_tool_set_has_3_tools_spec_expects_20_2026-08-25` |
| 7 | **tmux is required for most `workspace` commands.** | Without it every command except `add`/`remove`/`list` exits 1 with `tmux_unavailable`; the workspace system specs report `pending("BLOCKED: ...")`. | install tmux on the host |
| 8 | **Assistant replies are non-streaming.** `std.tui` has no incremental re-render. | Replies appear only after completion. | documented upgrade path, not scheduled |

## Live infrastructure evidence

`sh scripts/check/check-llm-caret-infra-live.shs` starts MinIO and greenmail
in Docker on free localhost ports, writes a temporary `llm_caret.sdn` with
secrets in env, runs `infra_servers_system_spec.spl` with the `*_LIVE=1`
gates, and tears its own containers down. Verdict is the last stdout line
(`PASS — 2 live row(s) executed …` / `FAIL` / `ERROR` exit 2 without Docker);
`--selftest` proves the verdict logic (a run with skipped rows never PASSes).
~10 s warm. The FTP row stays BLOCKED until `rt_ftp_*` is backed.

## Related

- Architecture: `doc/04_architecture/llm_caret_gui_backends.md`
- GUI design: `doc/05_design/llm_caret_gui_backends_gui.md`
- System manual: `doc/06_spec/03_system/app/llm_caret/feature/llm_caret_gui_backends_spec.md`
- Design: `doc/05_design/llm_caret_claude_cli_full_parity.md`
- Plan: `doc/03_plan/agent_tasks/llm_caret_claude_cli_full_parity_impl_plan.md`
- Trace gate (docs-coverage only): `llm_caret_claude_cli_harden.md`
