# LLM Caret — Usage Guide

Date: 2026-07-07

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
| `mail_list` | `mailbox` (default INBOX), `limit` (<=200) | read-only | IMAP `SELECT` + `FETCH` headers, `std.nogc_sync_mut.imap` |
| `mail_read` | `uid` | read-only | IMAP `UID FETCH (BODY.PEEK[])` |
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
names the variable, never a value. Specs:
`test/01_unit/app/llm_caret/infra_tools_spec.spl` (schemas, gating,
validation) and `test/03_system/app/llm_caret/infra_servers_system_spec.spl`
(live round trips, gated on `LLM_CARET_MAIL_LIVE=1` / `LLM_CARET_STORAGE_LIVE=1`
+ `LLM_CARET_CONFIG`; no in-repo SMTP/IMAP/S3/FTP server exists, so they are
honestly blocked on a bare host).

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

- Architecture: `doc/04_architecture/llm_caret_gui_backends.md`
- GUI design: `doc/05_design/llm_caret_gui_backends_gui.md`
- System manual: `doc/06_spec/03_system/app/llm_caret/feature/llm_caret_gui_backends_spec.md`
- Design: `doc/05_design/llm_caret_claude_cli_full_parity.md`
- Plan: `doc/03_plan/agent_tasks/llm_caret_claude_cli_full_parity_impl_plan.md`
- Trace gate (docs-coverage only): `llm_caret_claude_cli_harden.md`

### Live infrastructure evidence

`sh scripts/check/check-llm-caret-infra-live.shs` starts MinIO and greenmail
in Docker on free localhost ports, writes a temporary `llm_caret.sdn` with
secrets in env, runs `infra_servers_system_spec.spl` with the `*_LIVE=1`
gates, and tears its own containers down. Verdict is the last stdout line
(`PASS — 2 live row(s) executed …` / `FAIL` / `ERROR` exit 2 without Docker);
`--selftest` proves the verdict logic (a run with skipped rows never PASSes).
~10 s warm. The FTP row stays BLOCKED until `rt_ftp_*` is backed.
