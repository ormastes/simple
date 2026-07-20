# devhub — overview

`devhub` is the new primary name for the CLI implemented at `src/app/itf/`.
`bin/devhub` is the user-facing entry point; `bin/itf` stays as a permanent
compat alias (same binary, same dispatch table, both names resolve
identically — no deprecation warning planned). This document is the
top-level index for the devhub facade design; per-facade detail lives in the
sibling files listed under §7.

**Design posture: devhub is a unification/rename layer over `itf`'s existing
adapters and shared helpers (`flags.spl`, `output.spl`), not a rewrite.**
Every adapter function referenced across these docs already lives in
`src/app/itf/`.

---

## 1. Naming

| Name | Status | Notes |
|---|---|---|
| `devhub` | New primary name | User-facing, gh/mc/gmail-shaped grammar target |
| `itf` | Compat alias, permanent | Same binary/dispatch; existing scripts/muscle-memory keep working |
| `bin/devhub` | New wrapper | Points at the same build artifact as `bin/itf` |
| `bin/itf` | Existing wrapper | Unchanged |

Folder rename `src/app/itf/` → `src/app/devhub/` is **deferred** — see §6
rename plan.

---

## 2. The five facades

| Facade | Alias | Mimics | Backends |
|---|---|---|---|
| `email` | — | Gmail CLI UX | gmail (mail-cli IMAP/SMTP), outlook (Graph), outlook_imap (mail-cli IMAP/SMTP) |
| `task_manager` | `tasks` | gh-issue UX | jira, github |
| `web_storage` | `storage` | mc UX | minio (SigV4 native), s3-compatible via same adapter |
| `git` | — | gh UX | github, bitbucket |
| `wiki` | — | gh-like UX (gh has no wiki command; grammar is gh-flavored regardless) | confluence, github (`.wiki.git`) |

The overarching UX goal: an LLM or human user driving `devhub` should feel
like they're using `gh`/`mc`/`gmail`, regardless of which backend is actually
configured underneath.

---

## 3. Backend matrix

| Facade | Backend | Adapter file(s) | Shape |
|---|---|---|---|
| `task_manager` | github | `adapter_github.spl` (`gh_run`, subprocess wrapper around real `gh`) | passthrough |
| `task_manager` | jira | `adapter_jira.spl` (acli-backed) + `adapter_jira_curl.spl` (REST v3 fallback) | acli-first, curl-fallback |
| `git` | github | `adapter_github.spl` | passthrough |
| `git` | bitbucket | `adapter_bitbucket.spl` + `adapter_bitbucket_curl.spl` twin | PR-scoped only today |
| `wiki` | confluence | `adapter_confluence.spl` | REST, ~1:1 with `cmd_wiki.spl` |
| `wiki` | github | none yet (git-shell over `<repo>.wiki.git`, see facade doc) | net-new module |
| `web_storage` | minio | `adapter_minio.spl` (SigV4, zero shell-out) | primary |
| `web_storage` | minio (mc escape hatch) | `adapter_minio_mc.spl` (shells to real `mc`, currently **unwired** — dead code, no caller) | fallback, needs wiring |
| `email` | gmail | `tools/mail-cli/` (bash/curl IMAP+SMTP) | full parity today |
| `email` | outlook | `src/app/itf/{cmd_outlook,adapter_outlook,adapter_outlook_curl}.spl` (Graph, app-only OAuth, single shared mailbox) | thin, missing search/send/label/star/archive/draft |
| `email` | outlook_imap | `tools/mail-cli/` preset `outlook` | full parity today, no new code |

---

## 4. Config layout

**Current state (today, `itf`):** `~/.config/itf/auth.sdn` — single-endpoint
per backend. Relevant fields already present on `ItfConfig` (`config.spl`):
`confluence_url`, `confluence_user`, `confluence_default_space`, `jira_url`,
`jira_acli_path`, `jira_email`, `default_output`, `color_mode`,
`editor_override`, `pager_override`, `token_cmds`. MinIO reads its own
`[minio]` section (single alias, no multi-endpoint concept). Outlook reads a
`[outlook]` section (`tenant_id`, `client_id`, `client_secret_env`,
`shared_mailbox`).

**Devhub alias (later):** once the folder rename lands, the same file is
expected to also resolve under `~/.config/devhub/auth.sdn` (or the `itf` path
symlinked/aliased) — not yet implemented, tracked under §6.

**Known forward-looking divergence, not yet reconciled:** the `email` facade
research (`facade_email.md` §6) proposes a *dedicated*
`~/.config/devhub/email.sdn` multi-account schema (`accounts: {name: {provider,
email, ...}}`) distinct from `auth.sdn`'s single-section-per-backend shape.
Treat this as a **per-facade proposal for a richer multi-account config**, not
a contradiction of the "config lives in `~/.config/itf/auth.sdn` today"
baseline — `email.sdn` is new, additive, and unimplemented; it does not
replace `auth.sdn`'s existing sections for the other facades. The `storage`
facade has an analogous open question (single- vs multi-alias config, see
`facade_storage.md` §multi-alias). Both should be resolved together before
either facade's config work starts, since both are "does `auth.sdn` grow
named sub-sections, or does a facade get its own file" — the same structural
question asked twice.

---

## 5. Cross-cutting decisions (D1–D8)

These are gh-research-derived load-bearing calls; getting them wrong makes
every per-facade command table cosmetic. D1–D6 originate in the `task_manager`
research and generalize to `git`; D7/D8 are `wiki`/noun-verb specific but
apply devhub-wide.

| # | Decision | Rule |
|---|---|---|
| **D1** | `--backend {jira\|github\|all}` / `{github\|bitbucket}` / `{confluence\|github}` precedence | Explicit `--backend` flag > per-facade config default (`tasks.default_backend`, `git.default_backend`, `wiki.default_backend` — new `ItfConfig` fields, gap G6) > error listing which backends are configured (`itf auth status`-style). Never guess silently. |
| **D2** | `--search` / free-text query is backend-native, never translated | gh's `-S/--search` and `gh search issues/prs` take GitHub search-qualifier syntax verbatim; Jira's equivalent is JQL. devhub passes each straight through per-backend (matches `_jira_search`/`_github_list` contracts exactly). `--backend all` with a raw query prints a warning that the same string goes to both engines verbatim and results may differ in kind, not just content. |
| **D3** | `@me` / assignee synthesis | GitHub's `"@me"` is a literal gh resolves server-side — pass through unchanged. Jira has no such literal in JQL; `--assignee @me` must synthesize `assignee = currentUser()` inside the adapter layer (new `jira_build_list_jql(...)`, gap G1), not the CLI layer. |
| **D4** | `--state {open\|closed\|all}` mapping | Clean 1:1 for GitHub. For Jira, mapped through JQL `statusCategory`: `open` → `statusCategory != Done`, `closed` → `statusCategory = Done`, `all` → omit clause. Lives in the same `jira_build_list_jql` gap-fn as D3. |
| **D5** | Jira transitions ≠ gh's fixed open/closed state machine | gh issues are exactly `open`/`closed` (+ close reason). Jira issues move through an arbitrary per-project workflow graph. `tasks close` on jira = `jira_transition_issue(key, <configured done-status>)`; `tasks edit --status X` = `jira_transition_issue(key, X)` directly. Requires a configured target status name (`tasks.jira_done_status`, default `"Done"`) since "closed" isn't first-class in Jira. |
| **D6** | `--backend all` output shape | Add a `BACKEND` column first (before `NUMBER`/`KEY`) on every table — gh has none since gh is always single-backend. Sort merged rows by `--sort` if given, else backend-grouped. Partial failure: print the successful backend's table + a `print_warning` per failed backend; never fail the whole command. Exit 0 if ≥1 backend succeeded (matches gh's own tolerance for partial data). |
| **D7** | Noun-verb nesting | gh is strictly noun-then-verb (`gh pr list`). `devhub git` needs two nouns (`repo`, `pr`) exactly like gh. `devhub tasks` and `devhub wiki` each have exactly one implicit noun (issue, page) — collapse to verb-only (`devhub tasks list`, `devhub wiki view`), matching the existing `cmd_jira.spl`/`cmd_wiki.spl` shape rather than forcing an artificial `devhub tasks issue list`. State this once in top-level `--help`. |
| **D8** | Wiki space vs. `-R/--repo` | Do not force Confluence spaces into `OWNER/REPO` shape. Keep `--space KEY` as the canonical flag (matches `cmd_wiki.spl` today); optionally accept `-R`/`--repo` as a gh-familiar alias devhub maps 1:1 onto `--space` for `--backend confluence`, and onto the actual git repo (for wiki-clone purposes) when `--backend github`. |

---

## 6. Rename plan — `src/app/itf` → `src/app/devhub` (DEFERRED)

Deferred to avoid parallel-agent conflicts on a widely-imported path during
active development. Tracked as explicit TODOs rather than silently left
implicit:

- `DONE(devhub-rename, 2026-07-20)`: move `src/app/itf/` → `src/app/devhub/` (directory
  rename, all files carried over verbatim as a first pass — no logic changes
  in the same commit).
- `DONE(devhub-rename, 2026-07-20)`: update every `use app.itf.*` import path repo-wide
  to `use app.devhub.*` (grep-and-replace pass; must be its own commit,
  separated from any functional change, to keep the diff reviewable).
- `DONE(devhub-rename, 2026-07-20)`: update `main.spl`'s dispatcher so both `devhub` and
  `itf` invocation names resolve to the same match arms (today only `itf`
  exists as the binary name); add `bin/devhub` wrapper alongside the existing
  `bin/itf` wrapper, both pointing at the same compiled artifact.
- `DONE(devhub-rename, 2026-07-20)`: update `.claude/skills/*.md` references that
  currently say `itf` (e.g. `minio.md`, `repo_and_pull_req` sub-skills) to
  document `devhub` as primary with `itf` noted as the compat alias.
  Skill-name-based routing/dispatch strings must not break.
  `company_bug_report`'s routing to `itf` also needs a pointer update.
  `.mcp.json`/`code-style.md`'s MCP server table is unaffected (different
  binaries), but any doc that says `bin/itf <facade>` should gain a
  `bin/devhub <facade>` primary form.
  Note: the code-style table lists `simple-mcp`/`simple-lsp-mcp`/`t32-*` MCP
  servers, none of which are itf-derived — no change needed there beyond
  double-checking no stray `itf` cross-reference exists.
- `DONE(devhub-rename, 2026-07-20)`: update `doc/` cross-references that link into
  `src/app/itf/*.spl` paths (architecture docs, any existing itf guide) once
  the move lands, so links don't 404.
- `DONE(devhub-rename, 2026-07-20)`: after the move, confirm `ItfConfig`/`auth.sdn`
  naming — decide whether the config struct/file names also rename
  (`ItfConfig` → `DevhubConfig`, `~/.config/itf/` → `~/.config/devhub/`) or
  stay as a stable on-disk/struct name independent of the source-folder
  rename (recommend: keep `~/.config/itf/auth.sdn` as the on-disk path for
  backward compatibility even after the source rename, matching the
  `bin/itf` compat-alias precedent — avoid forcing existing users to
  re-auth).

None of the above is scoped as part of this design pass; this section exists
so the rename isn't lost track of.

---

## 7. Implementation phases

**P1 — cheap passthrough wins.** Four one-line match-arm additions to
`cmd_github.spl`, wiring subcommands `gh` already supports natively but
`itf`/devhub never exposed:
- `task_manager edit` → `issue edit` passthrough (gap **G5**)
- `git repo clone` → `repo clone` passthrough (gap **G9**)
- `git pr create` → `pr create` passthrough (gap **G11**)
- `git pr review` → `pr review` passthrough (gap **G13**)

Also in P1: `git repo list` wiring gap (**G8**, `_github_repo` currently only
has a `view` case). All five are trivial, no adapter logic needed, highest
value-per-effort in the whole design.

**P2 — tasks + storage + email facades.** The bulk of net-new adapter logic:
- `task_manager`: **G1** `jira_build_list_jql(...)` (JQL synthesis from
  `--assignee/--label/--state/--milestone/--search`, unblocks D2–D4 at once —
  single highest-value tasks-facade gap); **G1b** Jira label/assignee
  add/remove via `edit` (needs a source check of `acli jira workitem`
  capabilities, flagged as "needs research," not designed blind); **G6**
  config fields (`default_backend` × 3 facades, `jira_done_status`, Bitbucket
  workspace/repo config defaults).
- `web_storage`: object `rm` (new signed `DELETE` in `adapter_minio.spl` —
  smallest net-new addition that makes the facade useful day one); client-side
  `du` (pure aggregation over existing `minio_list_objects`); wiring
  `adapter_minio_mc.spl` into dispatch (currently zero callers) so binary
  `cp`/recursive `ls` can fall back to it instead of dead-ending on
  `minio_put_object`'s stub; `mirror` (loop of `ls`+`cp`, or `mc mirror`
  wrapper); alias/config model decision (single- vs multi-endpoint, see
  `facade_storage.md`).
- `email`: `mail_imap_search_raw` (`X-GM-RAW` passthrough, Gmail-only) +
  fixing the pre-existing `mail_format_summary_line` flags-always-`""` bug;
  `adapter_outlook.spl` additions — `outlook_search_messages`,
  `outlook_send_message`, `outlook_reply_message`, `outlook_set_flag`,
  `outlook_set_categories`; `cmd_outlook.spl` wiring for
  `search|send|reply|forward|star|label|archive|draft`.

**P3 — wiki git-shell module + bitbucket adapter gaps.** The two facades with
no REST path at all for part of their surface:
- `wiki --backend github`: net-new `adapter_github_wiki.spl` module —
  `clone_or_sync(repo) -> path`, `list_pages`, `read_page`, `write_page`,
  `delete_page`, `grep_pages`, all git-shell/filesystem based over
  `<repo>.wiki.git` (gaps **G14–G16**; no REST/GraphQL surface exists for
  GitHub wikis at all, confirmed against `gh --help`).
- `git --backend bitbucket`: **G7**/**G7b** (`bb_get_repo`/`bb_list_repos` —
  Bitbucket adapter is 100% PR-scoped today, no repo-level fns exist);
  **G10** (`bb_list_prs` — Bitbucket has zero PR-listing today, the single
  biggest bitbucket-side hole); **G12** (`pr checkout` — git-shell
  composition using data `bb_get_pr` already returns, not a new REST fn).

---

## 8. Sibling documents

- `facade_tasks_git_wiki.md` — command tables + gaps for `task_manager`,
  `git`, `wiki`.
- `facade_storage.md` — command tables + gaps for `web_storage`.
- `facade_email.md` — command tables + gaps for `email`.
