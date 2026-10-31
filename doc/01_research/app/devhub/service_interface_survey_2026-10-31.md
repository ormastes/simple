# DevHub service interface survey (2026-10-31)

Requirement: every DevHub interface follows the most famous interface of its
service kind (`gh` for git hosting, Gmail semantics for mail, `mc`/S3 for object
storage), whatever the backend. Paths are relative to `src/app/devhub/` unless
they start with a top-level directory. Facts come from reading the code on
`release/1.0.0` at `bf38288bef2`, except where a line is marked **probed**, which
means it was run on the Windows Phase 1 seed against the loopback emulator
(`test/fixtures/devhub/emulated/`). "Not read" is stated where a spec was only
grepped.

"GitBucket" has no hits in `src/`, `doc/` or `.claude/`. This survey takes the
request's "gitbucket" to mean Bitbucket.

## Cross-cutting findings

- **Before this work no DevHub HTTP spec except one used a live server.** The only
  live listener is `minio_binary_put_spec` (a Python `ThreadingHTTPServer`, needs
  `DEVHUB_*_BIN`/`DEVHUB_PYTHON_BIN`). Grep for `TcpListener`/`process_spawn` under
  `test/**/devhub/**` returned nothing.
- **Retry is uneven, and Retry-After is unreachable on curl paths.** `retry.spl:8-12`
  states `bb_should_retry` and `_outlook_should_retry` are unwired scaffolding.
  Curl paths use `-w http_code` and never capture response headers
  (`adapter_bitbucket.spl:206`: "Retry-After is not captured").
- **Retry wait shells to `sleep`** (`retry.spl:87`). On a Windows host without
  MSYS on `PATH` the wait is silently skipped, because the result is ignored.
- **Scheme checks:** the only one found is `messenger/config.spl:731-738`. Other
  backends accept `http://127.0.0.1:PORT`, which is what makes the emulator possible.
- **`accept_timeout` on Windows returns a non-blocking stream**
  (`src/compiler_rust/runtime/src/value/net_tcp.rs:426-428`; **probed**). See
  `doc/08_tracking/bug/tcp_accept_timeout_nonblocking_stream_windows_2026-10-31.md`.

## Git hosting: famous interface `gh`

| | GitHub | Bitbucket |
|---|---|---|
| Entry | `handle_git` `cmd_git.spl:73-82` -> `handle_github` | `_git_bitbucket` `cmd_git.spl:131` -> `gh_compat.spl`, `cmd_bb.spl` |
| Verbs | `pr` list/view/create/merge/review/checkout, `issue` list/view/create/edit/comment/close, `repo` view/clone (`cmd_github.spl:48-123`) | `pr` create/view/list, `repo` list/view, comment list/post, approve, merge, status (`cmd_bb.spl:48-58,148-152,288-290,377-379`) |
| Transport | `process_run_bounded(gh)`, `DEVHUB_REAL_GH` override (`adapter_github.spl:31,55`) | `process_run("curl")` (`adapter_bitbucket.spl:284`) |
| Point at loopback | **probed:** real gh with `GH_HOST=github.localhost`, `HTTP_PROXY=http://127.0.0.1:PORT` reaches the emulator in plain HTTP | `[bitbucket] url` (`config.spl:44`), or `base_url` field |

Backend order: `--backend` > `DEVHUB_GIT_BACKEND` > repo config > user config >
origin host (`backend_resolve.spl:93-105`). A non-bitbucket.org URL resolves to Data
Center unless `deployment: cloud` is set (`atlassian_site.spl:204-220`).
`adapter_bitbucket_curl.spl` has no importers in `src/`, so the command layer uses
`adapter_bitbucket.spl`.

**Gaps against `gh`**

- GitHub through `devhub gh`: not a true passthrough, despite the comment at
  `cmd_git.spl:75`. `pr diff/checks/close/reopen/edit/comment/status`, `issue reopen`,
  `repo list` and `gh api` fail with `unknown github pr command: {sub}` or its
  equivalent (`cmd_github.spl:37,73,109,132`), though help advertises `pr comment`,
  `pr status` and `repo list` (`cmd_git.spl:312-313`). `bin/gh` itself execs real gh
  (`bin/gh:132`) and has no such gap.
- Bitbucket, typed refusals (`gh_compat.spl`, allowlist at `:185-190`):
  - `pr diff/checks/close/reopen/edit/ready`: `:442`
  - `gh issue`, `gh api`: "supported nouns: pr, repo" (`cmd_git.spl:144`)
  - `pr list --search/--label/--draft/--web`: `:323,383`
  - `pr list --author/--assignee/--base`: `:315`
  - `pr create --draft/--fill`, `merge --auto/--delete-branch`, `view --comments`: `:363,375,394`
  - `pr review` without `--approve`: `:425`
- Bitbucket, silent differences: `closed` means DECLINED only (`:94`); `isDraft` is
  hardcoded false (`:142`); no decline function exists in the adapter.

**Existing tests:** `gh_compat_spec`, `gh_json_roundtrip_spec`, `backend_resolve_spec`,
`adapter_bitbucket_spec` are pure or use a prevention mock. `cmd_github_spec` uses a
fake gh script. `gh_shim_backend_routing_spec` runs real `bin/gh`, no HTTP socket.
None exercised a socket.

## Issues: famous interface `gh issue`

- Entry: `tasks` list/view/create/comment/close/edit/search (`cmd_tasks.spl:71-83`,
  `--backend jira|github|all`); `jira` view/search/create/update/comment/transition
  (`cmd_jira.spl:25-35`).
- Transport: `acli` first when no token (`adapter_jira.spl:42`), otherwise curl
  (`adapter_jira_curl.spl:120`). `jira.url` -> `JiraClient.base_url`
  (`cmd_jira.spl:199,205`). `/rest/api/3` on Cloud, `/2` on Data Center
  (`atlassian_site.spl:148-154`).
- **Gaps:** no `reopen`, `delete`, `pin`, `transfer`, `lock`, `status` on any backend.
  `tasks list` reads only assignee, label, state, search, limit
  (`cmd_tasks.spl:275-279`), so no `--author`. Jira label/assignee edit: "not yet
  supported for the jira backend" (`:597`). `--backend all` refused for single items
  (`:184`).
- **Existing tests:** `cmd_tasks_spec`, `cmd_jira_spec` use fake `gh`/`acli`/`curl` on
  `PATH`. `adapter_jira_curl_spec` has no loopback. `jira_adf_spec`,
  `jira_token_auth_spec` not read. None exercised a socket.

## Wiki: no single famous CLI

- Entry: list/ls, view, edit, create, delete/rm, search (`cmd_wiki.spl:47-91`); `-R`
  mirrors gh (`:142`).
- Transport: Confluence `sosix_process_run("curl")` (`adapter_confluence.spl:135`) on
  REST v1. `confluence.url` or `confluence_gateway_url` (`:67`). GitHub wiki shells to
  `git`, with `DEVHUB_WIKI_CLONE_URL_OVERRIDE` (`wiki_git.spl:116`).
- **Gaps:** no history, move, attachment, comment or label verbs; `--web` on GitHub
  hardcodes github.com (`cmd_wiki.spl:475,508`).
- **Existing tests:** `wiki_git_spec`, `wiki_backend_routing_spec` use real git on a
  local bare repo. `wiki_confluence_no_recursion_spec:23,28` uses real curl to closed
  port 9, no listener. `confluence_gateway_spec` not read; `confluence_access_spec`
  offline fixtures. None exercised a Confluence server.

## Object storage: famous interface `mc` / S3

- Entry: `storage` ls/cp/cat/stat/mb/rb/rm/presign/presign-put/du/mirror/health
  (`cmd_storage.spl:35-57`); `minio` ls/get/put/stat/presign/presign-put/mb/rb/rm/health
  (`cmd_minio.spl:28-46`).
- Transport: `rt_http_request` for most calls, `rt_http_download` for downloads
  (`adapter_minio.spl:514`), `curl_request_bytes` for Windows binary PUT (`:852-863`).
  **Probed:** `rt_http_request` DOES transmit on the Windows seed
  (`minio_list_buckets` passed emulator SigV4 recomputation), despite the workaround
  note `windows_core_http_client_unavailable_2026_10_27` at `:851`.
- **Gaps:** multipart refused at 64 MiB (`adapter_minio.spl:31,667,828`); no delimiter
  mode (`cmd_storage.spl:120`); `stat` falls back to ListObjectsV2 because headers are
  not exposed (`adapter_minio.spl:577`); remote-to-remote copy refused
  (`cmd_storage.spl:821`); no batch DeleteObjects, bulk cap 1000 (`:259`); `mirror`
  compares size only (`:965`); no `mv`, `find`, `tree`, tags, versioning, retention.
  `adapter_minio_mc.spl` has no importers, so `mc` is unreachable from dispatch.
- **Existing tests:** `minio_binary_put_spec` uses a real socket (Python server).
  `cmd_storage_spec` is validation and pure functions. `adapter_minio_spec`,
  `aws_sigv4_spec` have no loopback.

## Mail: famous interface Gmail

- Entry: `email` inbox, read, send, reply, forward, search, label, star, archive, draft,
  auth (`cmd_email.spl:174-193`); `outlook` folders, messages, get, move, mark
  (`cmd_outlook.spl:45-53`).
- Transport: gmail/imap go to the external bash `tools/mail-cli/bin/mail` via
  `process_run_bounded` (`email_support.spl:323-326,366`). Outlook: `send_request`
  (`adapter_outlook.spl`) and curl (`adapter_outlook_curl.spl`); `base_url` is a field
  with no config key; constructors hardcode Graph (`adapter_outlook.spl:100,112`,
  `adapter_outlook_curl.spl:57`); token URL hardcoded (`:80`).
- **Gaps, Gmail-style backends:** only from, subject, after, before, newer_than,
  older_than and free text reach search; `to:`, `is:`, `has:`, `label:`, OR, negation are
  warned and dropped (`cmd_email.spl:359-393`). `label --add`/`--remove` "not yet
  supported" (`:600,609`). `star --off` refused (`:628`). `reply --all` only warns
  (`:511`). No thread view/modify, trash, spam or mark-read. Help still claims "full
  parity" (`:746,748`).
- **Gaps, Outlook:** only inbox, read, archive; the rest return "not yet supported on
  outlook backend" (`email_support.spl:403`). Inbox ignores `--unread`/`--threads`,
  hardcodes `unread: false`, `labels: []` (`cmd_email.spl:236-251`). No `$search`
  (`adapter_outlook.spl:304`).
- **Gaps, POP3:** "POP3 does not support {action}" (`cmd_email.spl:160`).
- **Existing tests:** `email_cmd_spec` uses a fake mail script; `adapter_outlook*_spec`
  no loopback; `shared_mail_sdn_acceptance_spec` real mail-cli config, no server.

## Others

- `api`: GET/POST/PUT/DELETE; PATCH refused (`cmd_api.spl:36`), unlike `gh api`.
  `rt_http_request` (`:84`).
- `daily-debug`: Outlook curl adapter only (`cmd_daily_debug.spl:16-20`).
- `messenger`: local SQLite/SQLCipher readers; "No send ever executes"
  (`cmd_messenger.spl:196-203`). No network protocol to emulate.
- `lifecycle`: local-only, `"remote_mutation":"disabled"` (`cmd_lifecycle.spl:63`).
