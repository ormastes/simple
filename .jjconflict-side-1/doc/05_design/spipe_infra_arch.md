# SPipe Infra Arch — Daily Debug + 3-Level Review + Bug-Report Ingest

Tracking issue: [#10](https://github.com/ormastes/simple/issues/10)

Inputs:
- [Bitbucket REST 2026 research](../01_research/local/spipe_infra/bitbucket_rest_2026.md)
- [Microsoft Graph mail 2026 research](../01_research/local/spipe_infra/microsoft_graph_mail_2026.md)
- [MinIO S3 2026 research](../01_research/local/spipe_infra/minio_s3_2026.md)

## Scope

Extend `/spipe` (formerly `/sspec`) into a daily-operating dev pipe with bug-report ingest, multi-provider infra, and a 3-level review pipeline. Plug into the existing ITF adapter pattern (`adapter_jira`, `adapter_github`, `adapter_confluence`) and the `repo_and_pull_req` plugin (sub-skill trees `git/`, `jira/`, `bug/`, `mail/`).

## File layout (new code)

| Path | Purpose |
|------|---------|
| `src/app/itf/adapter_minio.spl` | S3-compatible client (HTTP + SigV4) |
| `src/app/itf/cmd_minio.spl` | `itf minio {ls,get,put,stat,presign,health}` |
| `src/app/itf/adapter_bitbucket.spl` | Bitbucket Cloud REST 2.0 client |
| `src/app/itf/cmd_bb.spl` | `itf bb {pr,comment,approve,merge,status}` |
| `src/app/itf/adapter_outlook.spl` | Microsoft Graph mail client (replaces deprecated v2.0) |
| `src/app/itf/cmd_outlook.spl` | `itf outlook {folders,messages,get,move,mark}` |
| `src/lib/nogc_sync_mut/aws_sigv4.spl` | SigV4 helper (driven by MinIO test vector `aeeed9bb…`) |
| `src/lib/nogc_sync_mut/oauth2.spl` | OAuth2 client-credentials + token cache (driven by Graph) |
| `.claude/skills/company_bug_report.md` | Dispatcher: mail → jira → minio → triage |
| `tools/claude-plugin/repo-and-pull-req/skills/bb/bb_setup.md` | Install + Repo Access Token |
| `tools/claude-plugin/repo-and-pull-req/skills/bb/bb_push.md` | Push + PR create |
| `tools/claude-plugin/repo-and-pull-req/skills/bb/bb_pull_req_review.md` | PR review pass |

Touched (extended, not rewritten):
- `tools/claude-plugin/repo-and-pull-req/agents/review_loop.md` — add `--level=1|2|3`
- `.claude/skills/spipe_loop.md` — add `--daily-debug` mode
- `.claude/skills/repo_and_pull_req.md` — add `--target=gh|bb|jira`, `--level=N` dispatch
- `src/app/itf/auth.spl` — schema additions (below)

## auth.sdn schema (additions)

```sdn
[bitbucket]
url = https://api.bitbucket.org/2.0
workspace = <ws_slug>
token = <repository_access_token>   # Bearer; App Passwords deprecated 2026

[minio]
url = https://minio.example.com:9000
region = us-east-1
access_key = <key>
secret_key = <secret>
tls_skip_verify = false               # warn loudly if true

[outlook]
tenant_id = <tenant_id>
client_id = <app_id>
client_secret_env = GRAPH_CLIENT_SECRET   # env var name; never inline secret
shared_mailbox = bugs@example.com
base_url = https://graph.microsoft.com/v1.0
```

Token cache (auto-managed, mode 0600):
- `~/.config/itf/outlook_token_cache.sdn` — Graph access token (1h TTL, re-request before expiry)

## Adapter pattern (mirror existing ITF)

Each adapter file:
1. `class FooClient` with config, http_client, auth_header().
2. Per-endpoint `fn foo_<verb>(client, args) -> (success: bool, parsed: T, raw_json: text)` matching the `jira_view_issue` / `jira_search` shape.
3. All HTTP via `src/lib/nogc_sync_mut/http_client/` (no subprocess curl).
4. JSON parse via `std.common.json`. XML parse for S3 via new helper in `aws_sigv4.spl` (small subset).

Each `cmd_*.spl`:
1. `fn handle_<provider>(args: [text]) -> i64` with subcommand dispatch.
2. `--json` flag honored via `wants_json(args)`; text output via `print_table_*`.
3. `_print_<provider>_help()` follows existing style.

## 3-Level Review State Machine

State extends existing `.review/<pr-number>/state.json`:

```json
{
  "pr_number": 42,
  "target": "gh|bb|jira",
  "level": 1|2|3,
  "approver": "codex|claude|human",
  "bot_approved": false,
  "human_approved": false,
  "checks_passing": false,
  "merge_attempted": false,
  "cycle_count": 0,
  "last_check": "2026-04-26T12:00:00Z",
  "status": "reviewing|awaiting-bot|awaiting-human|awaiting-checks|merged|closed|blocked"
}
```

Per-cycle procedure (per `--level`):

| Step | L1 | L2 | L3 |
|------|----|----|----|
| Post review comments | yes | yes | yes |
| Bot approves PR via API | — | yes (if review verdict = approve) | — |
| Wait for human approval | — | — | yes |
| Wait for checks green | — | yes | yes |
| Merge to main | — | yes (when checks + bot approved) | yes (when checks + human approved) |
| Cycle cadence | one-shot | poll 60s up to 24h | poll 5m up to 7d |

**Bot-reviewer detection (Codex-first per user decision):**
1. Probe Codex availability via `/codex:setup` (existing skill).
2. If available and not quota-exceeded: dispatch via `codex:rescue` agent with the PR diff; capture verdict (`approve|request-changes|comment`).
3. If unavailable or returned `comment`: fall back to a fresh Claude general-purpose agent with the same prompt.
4. Only `approve` from the bot triggers `POST .../approve` (gh/bb/jira). `request-changes` posts inline comments and resets the cycle.

**Approve API per target:**
- GitHub: `gh pr review --approve` (existing).
- Bitbucket: `POST /repositories/{ws}/{repo}/pullrequests/{id}/approve` with Bearer token.
- Jira: not applicable (Jira tracks the issue, not the code review — L2/L3 work on gh/bb only; Jira is for ticket linking).

**Merge API per target:**
- GitHub: `gh pr merge --squash`.
- Bitbucket: `POST .../pullrequests/{id}/merge` with `merge_strategy=squash`, `close_source_branch=true`.

## Daily Debug Analysis (`spipe_loop --daily-debug`)

Pipeline (one cycle, idempotent on re-run):

1. **Watermark load** — read `~/.config/itf/spipe_daily.sdn` for `last_run`.
2. **Pull bug mail** — `outlook.list_messages(folder=Inbox, $filter=receivedDateTime ge last_run)` (or Gmail/IMAP backend if configured).
3. **Per message**:
   - Extract Jira key from subject/body via regex `[A-Z][A-Z0-9]+-\d+`.
   - `jira_view_issue(key)` → ticket metadata.
   - Walk attachments + body for MinIO URLs (`https://minio.example.com:9000/<bucket>/<key>`).
   - For each MinIO ref: `minio.get_object` to `build/triage/YYYY-MM-DD/<ticket>/`.
4. **Triage** — heuristic categorize (FW build / crash dump / log / note) by extension and content sniff.
5. **Report** — write `doc/08_tracking/debug/YYYY-MM-DD.md` with:
   - Summary table (ticket, severity, owner, artifacts).
   - Per-bug section with mail summary, ticket excerpt, artifact paths.
6. **Watermark save** — atomic update of `last_run`.
7. **Optional notify** — `mail.send` digest to ops list (skipped on first run / `--quiet`).

## `company_bug_report` skill

Dispatcher pattern (mirrors `mail.md`, `bug_review.md`):

```
/company_bug_report ingest                # full daily cycle (calls spipe_loop --daily-debug)
/company_bug_report fw <ticket>           # download FW only
/company_bug_report dump <ticket>         # download crash dump only
/company_bug_report notes <ticket>        # fetch eng notes only
/company_bug_report find-key <ticket>     # extract key facts (severity, owner, target SoC)
```

Routes to:
- `mail` skill for mail listing/reading
- `bug_review` skill for triage
- `repo_and_pull_req` for PR creation when fix is identified
- New direct ITF calls (`itf minio get`, `itf jira view`)

## Sstack Phase 8 (ship) wiring

`/sstack` ship phase accepts new args:
- `--target=gh|bb` (default: detect from origin URL)
- `--review-level=1|2|3` (default: 1)

Threads through to `repo_and_pull_req push --target --level`.

## Codex-first / Claude-fallback (user decision)

Per the existing sstack pattern:
1. Probe Codex CLI: `codex --version` (or per `/codex:setup`).
2. If present and not rate-limited: spawn via `codex:rescue` agent.
3. Else: spawn Sonnet general-purpose agent.
4. Log decision in state file (`approver: codex|claude`).

## What's deferred (out of scope for issue #10)

- GitLab adapter
- Webhook subscriptions (push events instead of polling) for any provider
- Production scheduling (cron / `/schedule`) — skill exists; user invokes manually
- Confluence digest publishing (notify step `--quiet` by default)
- Bitbucket DC/Server (Cloud only)

## Open questions for user sign-off (Phase 4 gate)

1. **MinIO URL convention** — assume URLs in mail/Jira are `<minio_url>/<bucket>/<key>`? Or do bug reports use presigned URLs that need a different handler?
2. **Shared mailbox or personal Gmail** — for daily-debug, target a dedicated bug-report mailbox via Outlook+Graph (recommended) or read user's personal Gmail inbox folder?
3. **Approval semantics on Jira target** — when ship target = `jira`, treat L2/L3 as "comment + transition issue" rather than "approve PR"? Or skip Jira from L2/L3 entirely?
4. **Bot username for Bitbucket** — use the Repository Access Token's principal, or create a dedicated bot user?

## Implementation parallelization (Phase 5 plan)

Five disjoint sub-agent scopes (per memory note `feedback_parallel_scope_partition`):

| Agent | Scope | Files |
|-------|-------|-------|
| A | SigV4 + MinIO | `aws_sigv4.spl`, `adapter_minio.spl`, `cmd_minio.spl` |
| B | OAuth2 + Outlook | `oauth2.spl`, `adapter_outlook.spl`, `cmd_outlook.spl` |
| C | Bitbucket | `adapter_bitbucket.spl`, `cmd_bb.spl`, `bb/*.md` |
| D | Review L2/L3 wiring | `review_loop.md`, `repo_and_pull_req.md`, sstack ship |
| E | Skill + daily-debug | `company_bug_report.md`, `spipe_loop.md` --daily-debug |

Per-phase commits per memory note `feedback_sync_bundling_clobbers_commits`.
