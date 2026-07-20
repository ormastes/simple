# devhub — overview

**Status as of 2026-07-20:** all 5 facades (`task_manager`/`tasks`,
`git` (`github`+`bb`), `wiki`, `web_storage`/`storage`, `email`) are
implemented and dispatched from `src/app/devhub/main.spl`. The devhub spec
suite is **25/25 spec files green — 661 tests, 0 failed**
(`bin/simple test test/01_unit/app/devhub/`, verified 2026-07-20). The
folder rename (§6) landed at `edb584b24ad` ("refactor(devhub): rename
src/app/itf -> src/app/devhub ... Resolves TODO(devhub-rename)"). Every gap
id in §7's registry was re-walked against source this pass; see per-gap
status below — several are done under a different function name than
originally proposed, a few are still genuinely open.

`devhub` is the primary name for the CLI, implemented at `src/app/devhub/`.
`bin/devhub` is the user-facing entry point; `bin/itf` stays as a permanent
compat alias (same binary, same dispatch table, both names resolve
identically — no deprecation warning planned). This document is the
top-level index for the devhub facade design; per-facade detail lives in the
sibling files listed under §7.

**Design posture: devhub is a unification/rename layer over the former
`itf`'s existing adapters and shared helpers (`flags.spl`, `output.spl`),
not a rewrite.** Every adapter function referenced across these docs lives
in `src/app/devhub/` (post-rename; see §6).

---

## 1. Naming

| Name | Status | Notes |
|---|---|---|
| `devhub` | Primary name | User-facing, gh/mc/gmail-shaped grammar target |
| `itf` | Compat alias, permanent | Same binary/dispatch; existing scripts/muscle-memory keep working |
| `bin/devhub` | Wrapper | Runs `src/app/devhub/main.spl` |
| `bin/itf` | Compat wrapper | Runs `src/app/devhub/main.spl` — same artifact as `bin/devhub` |

Folder rename `src/app/itf/` → `src/app/devhub/` **landed** — see §6 for the
completed-state note (was previously tracked here as deferred).

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
| `wiki` | github | `wiki_git.spl` (`wiki_git_list/read/write/delete/search`, git-shell over `<repo>.wiki.git`) + `cmd_wiki.spl` (`_wiki_github_list/view/edit/create/delete/search`) | **done** — landed directly in the shared `wiki_git.spl` module rather than the originally proposed standalone `adapter_github_wiki.spl` (§7 G14–G16 note) |
| `web_storage` | minio | `adapter_minio.spl` (SigV4, zero shell-out) | primary |
| `web_storage` | minio (mc escape hatch) | `adapter_minio_mc.spl` (shells to real `mc`, currently **unwired** — dead code, no caller, reconfirmed 2026-07-20) | fallback, needs wiring |
| `email` | gmail | `tools/mail-cli/` (bash/curl IMAP+SMTP) | full parity today |
| `email` | outlook | `src/app/devhub/{cmd_outlook,adapter_outlook,adapter_outlook_curl}.spl` (Graph, app-only OAuth, single shared mailbox) | dispatch wired in `cmd_email.spl` (search/send/reply/forward/label all reachable), but the outlook-backend adapter fns (`outlook_search_messages`, `outlook_send_message`, `outlook_reply_message`, `outlook_set_categories`) are unimplemented — `_outlook_gap_error(...)` returns an honest per-verb gap error rather than a silent stub |
| `email` | outlook_imap | `tools/mail-cli/` preset `outlook` | full parity today, no new code |

---

## 4. Config layout

**Current state, verified in `config.spl` 2026-07-20:** config is **split
across two files**, both still under `~/.config/itf/` (kept as the on-disk
path for backward compat per §6, even though the source folder is now
`src/app/devhub/`):
- `~/.config/itf/config.sdn` (`config_path()`) — non-secret settings.
- `~/.config/itf/auth.sdn` (`auth_path()`) — tokens/credentials.

`config_dir()` resolves to `{userprofile}/.config/itf` on Windows and
`{home}/.config/itf` elsewhere — single-endpoint per backend, same as
before. Fields on `ItfConfig` (`config.spl`): `confluence_url`,
`confluence_user`, `confluence_default_space`, `jira_url`,
`jira_acli_path`, `jira_email`, `default_output`, `color_mode`,
`editor_override`, `pager_override`, `token_cmds` — **plus three fields
landed since the last pass** (gap G6, §7): `wiki_default_backend`,
`tasks_default_backend`, `tasks_jira_done_status` (all default to `""` /
unset, with each facade's command layer falling back to a hardcoded default
— `"confluence"`, `"github"`, `"Done"` respectively — when unset). MinIO
reads its own `[minio]` section (single alias, no multi-endpoint concept).
Outlook reads a `[outlook]` section (`tenant_id`, `client_id`,
`client_secret_env`, `shared_mailbox`). **Still missing:** a
`git.default_backend` field (D1 for `github`/`bitbucket`) and Bitbucket
workspace/repo config defaults — `cmd_bb.spl` still resolves those from
`--workspace`/`--repo` flags or `BB_WORKSPACE`/`BB_REPO` env vars only, not
from `config.sdn`.

**Devhub alias (later):** once broader devhub tooling wants a
`~/.config/devhub/` path, the same file is expected to also resolve there
(or the `itf` path symlinked/aliased) — not yet implemented, tracked under
§6, and not blocking today since `bin/itf`/`bin/devhub` already share one
binary and one config path.

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
| **D1** | `--backend {jira\|github\|all}` / `{github\|bitbucket}` / `{confluence\|github}` precedence | Explicit `--backend` flag > per-facade config default (`tasks.default_backend`, `wiki.default_backend` — real `ItfConfig` fields, gap G6, confirmed in `config.spl`) > error listing which backends are configured. **Confirmed 2026-07-20 for `tasks`/`wiki`** (`cmd_tasks.spl` `_tasks_backend_default()`, mirrored in `cmd_wiki.spl`). **Drift:** `git.default_backend` does not exist yet — `git`/`bb` backend selection still has no config-default step, only `--backend` or per-command flags (§7 G6 still-open note). |
| **D2** | `--search` / free-text query is backend-native, never translated | gh's `-S/--search` and `gh search issues/prs` take GitHub search-qualifier syntax verbatim; Jira's equivalent is JQL. devhub passes each straight through per-backend (matches `_jira_search`/`_github_list` contracts exactly). `--backend all` with a raw query prints a warning that the same string goes to both engines verbatim and results may differ in kind, not just content. **Confirmed 2026-07-20, with a minor nuance**: `_jira_build_list_jql(...)` (`cmd_tasks.spl:182`) wraps `--search` as `text ~ "{search}"` before handing it to Jira — a JQL free-text clause, not a byte-for-byte passthrough — while the GitHub path passes `--search`/`-S` through unchanged. Consistent with "backend-native," just not a literal string copy on the Jira side. |
| **D3** | `@me` / assignee synthesis | GitHub's `"@me"` is a literal gh resolves server-side — pass through unchanged. Jira has no such literal in JQL; `--assignee @me` must synthesize `assignee = currentUser()` inside the adapter layer (gap G1), not the CLI layer. **Confirmed 2026-07-20** — implemented exactly as `_jira_build_list_jql(...)` in `cmd_tasks.spl:182` (private helper, not in the adapter file as originally proposed — naming drift only, behavior matches). |
| **D4** | `--state {open\|closed\|all}` mapping | Clean 1:1 for GitHub. For Jira, mapped through JQL `statusCategory`: `open` → `statusCategory != Done`, `closed` → `statusCategory = Done`, `all` → omit clause. Lives in the same `_jira_build_list_jql` gap-fn as D3. **Confirmed 2026-07-20**, byte-for-byte match in source. |
| **D5** | Jira transitions ≠ gh's fixed open/closed state machine | gh issues are exactly `open`/`closed` (+ close reason). Jira issues move through an arbitrary per-project workflow graph. `tasks close` on jira transitions to a configured target status; `tasks edit --status X` transitions directly. Requires a configured target status name (`tasks.jira_done_status`, default `"Done"`) since "closed" isn't first-class in Jira. **Confirmed 2026-07-20** — `tasks_jira_done_status` is a real `ItfConfig` field (`config.spl`), read via `_tasks_jira_done_status()` in `cmd_tasks.spl`. |
| **D6** | `--backend all` output shape | Add a `BACKEND` column first (before `NUMBER`/`KEY`) on every table — gh has none since gh is always single-backend. Sort merged rows by `--sort` if given, else backend-grouped. Partial failure: print the successful backend's table + a `print_warning` per failed backend; never fail the whole command. Exit 0 if ≥1 backend succeeded (matches gh's own tolerance for partial data). **Confirmed present** in `cmd_tasks.spl` (`--backend all` merge path); not re-audited cell-by-cell this pass. |
| **D7** | Noun-verb nesting | gh is strictly noun-then-verb (`gh pr list`). `devhub git` needs two nouns (`repo`, `pr`) exactly like gh. `devhub tasks` and `devhub wiki` each have exactly one implicit noun (issue, page) — collapse to verb-only (`devhub tasks list`, `devhub wiki view`), matching the existing `cmd_jira.spl`/`cmd_wiki.spl` shape rather than forcing an artificial `devhub tasks issue list`. State this once in top-level `--help`. **Confirmed** — `cmd_tasks.spl`/`cmd_wiki.spl` dispatch on bare verbs, `cmd_github.spl`/`cmd_bb.spl` dispatch on `pr`/`repo` nouns first. No drift. |
| **D8** | Wiki space vs. `-R/--repo` | Do not force Confluence spaces into `OWNER/REPO` shape. Keep `--space KEY` as the canonical flag (matches `cmd_wiki.spl` today); optionally accept `-R`/`--repo` as a gh-familiar alias devhub maps 1:1 onto `--space` for `--backend confluence`, and onto the actual git repo (for wiki-clone purposes) when `--backend github`. **Confirmed 2026-07-20** — `cmd_wiki.spl` reads `--space`/`--repo`/`-R` flags as described. |

---

## 6. Rename plan — `src/app/itf` → `src/app/devhub` (DONE)

**Rename completed 2026-07-20**, landed at `edb584b24ad`
("refactor(devhub): rename src/app/itf -> src/app/devhub + test dirs;
rewrite app.itf.* imports, path refs in cli dispatch/scripts/skills/live
specs; fix argv scanner ends_with pattern; bin/itf stays as compat wrapper.
Resolves TODO(devhub-rename)"). Final layout, each item verified against
source this pass:

- Directory: `src/app/devhub/` is the real (`git mv`'d) source tree; all
  `use app.itf.*` imports were rewritten to `use app.devhub.*` in the same
  commit (confirmed in `main.spl`, `cmd_*.spl`, `adapter_*.spl`).
  `test/01_unit/app/devhub/` is the corresponding test tree (25 spec files,
  §7 test evidence).
- Dispatcher: both `bin/devhub` and `bin/itf` are thin `sh` wrappers that
  resolve a Simple runtime and `exec` `src/app/devhub/main.spl` — one
  compiled artifact, two invocation names, no separate `devhub` vs `itf`
  match-arm logic needed at the binary-name level.
- `bin/itf` **stays as a permanent compat wrapper**, unchanged in behavior
  from a user's perspective — same binary, same dispatch table.
- Config path: `~/.config/itf/config.sdn` + `~/.config/itf/auth.sdn` are
  kept as the on-disk paths for backward compatibility (see §4) — the
  config struct is still named `ItfConfig` and no `~/.config/devhub/` path
  exists yet. This matches the recommendation this section previously
  tracked as an open decision.
- Skills/docs cross-references: the rename commit's diffstat touched
  `src/app/cli/dispatch/table.spl` and `src/app/cli/_CliMain/main_and_help.spl`
  alongside the source move; a residual sweep of `.claude/skills/*.md` and
  other `doc/` cross-references for stray `src/app/itf/*.spl` links was not
  re-verified in this docs-only pass — flag as a follow-up if any turn up
  stale.

*Footnote: a transient jj-conflict state was observed in the working copy at
doc-review time, unrelated to devhub's design — see this pass's tracking
notes, not this spec, for VCS remediation. The commit above is the source
of truth for "done."*

---

## 7. Implementation phases

Gap registry re-walked against `src/app/devhub/*.spl` 2026-07-20 — every id
kept (none deleted); each now carries a Done/open verdict with the
implementing fn+file, or the reason it's still open.

**P1 — cheap passthrough wins.** Match-arm additions to `cmd_github.spl`,
wiring subcommands `gh` already supports natively but `itf`/devhub didn't
expose:
- `task_manager edit` → `issue edit` passthrough (gap **G5**) — **Done**:
  `cmd_github.spl` `"edit": _github_passthrough(["issue", "edit"] + rest)`.
- `git repo clone` → `repo clone` passthrough (gap **G9**) — **Done**:
  `cmd_github.spl` `_github_repo()`, `"clone"` arm.
- `git pr create` → `pr create` passthrough (gap **G11**) — **Done**:
  `cmd_github.spl` `_github_pr()`, `"create"` arm.
- `git pr review` → `pr review` passthrough (gap **G13**) — **Done**:
  `cmd_github.spl` `_github_pr()`, `"review"` arm.
- `git repo list` wiring (gap **G8**) — **Still open**. `_github_repo()`'s
  usage string is still `"itf github repo <view|clone> [name]"` — no `list`
  match arm exists. This is the one P1 item that did NOT land; everything
  else in P1 is done.

**P2 — tasks + storage + email facades.**
- `task_manager`: **G1** JQL synthesis from
  `--assignee/--label/--state/--search` — **Done**, as
  `_jira_build_list_jql(...)` in `cmd_tasks.spl:182` (private helper, not on
  the adapter as originally proposed — see D3/D4 naming-drift note in §5).
  **G1b** Jira label/assignee add/remove via `edit` — **still open**,
  self-documented in source: `_tasks_edit_jira()` in `cmd_tasks.spl` prints
  `"not yet supported for the jira backend (gap G1b — acli's label/assignee
  mutation surface needs research...)"` and returns exit 1 for
  `--add-label/--remove-label/--add-assignee/--remove-assignee`. **G6**
  config fields — **partially done**: `tasks_default_backend`,
  `wiki_default_backend`, `tasks_jira_done_status` are real `ItfConfig`
  fields (`config.spl`); `git.default_backend` and Bitbucket workspace/repo
  config defaults are still **not** fields (§4).
- `web_storage`: object `rm` — **Done**, `minio_delete_object()` in
  `adapter_minio.spl:601`, wired at `cmd_storage.spl`'s `"rm"` arm.
  Client-side `du` — **Done**, `_storage_du()` in `cmd_storage.spl:440`.
  `mirror` — **Done**, wired at `cmd_storage.spl`'s `"mirror"` arm. Wiring
  `adapter_minio_mc.spl` into dispatch — **still open**: reconfirmed zero
  callers of anything in `adapter_minio_mc.spl` from `cmd_storage.spl` or
  `main.spl`; the recursive-`ls`/binary-`cp` mc-fallback path described in
  the original design has not been wired. Alias/config model decision
  (single- vs multi-endpoint) — undecided, see `facade_storage.md`.
- `email`: X-GM-RAW passthrough — **Done**, `email_translate.spl` (Gmail
  path, §5a, 74 golden translation rows per the recent email-facade
  landing). `cmd_outlook.spl`/`cmd_email.spl` wiring for
  `search|send|reply|forward|star|label|archive|draft` — **dispatch Done**,
  all eight verbs are reachable in `cmd_email.spl`; but the underlying
  Outlook-backend adapter fns are **still open**: `outlook_search_messages`,
  `outlook_send_message`, `outlook_reply_message`, `outlook_set_categories`
  do not exist in `adapter_outlook.spl` — each verb calls
  `_outlook_gap_error("<verb>", "<fn-name>")` and returns an honest error
  rather than a silent no-op (matches the repo's "no fake stubs" bar). Not
  independently reverified: the pre-existing
  `mail_format_summary_line` flags-always-`""` bug fix mentioned in the
  original P2 text (no `mail_format_summary_line` hits in current source —
  may have been renamed or folded into a different fn; flag for the email
  facade doc to confirm).

**P3 — wiki git-shell module + bitbucket adapter gaps.**
- `wiki --backend github` (gaps **G14–G16**) — **Done**, but landed in the
  shared `wiki_git.spl` module rather than a standalone
  `adapter_github_wiki.spl` as originally proposed: `wiki_git_ensure_synced`
  (clone-or-sync), `wiki_git_list`, `wiki_git_read`, `wiki_git_write`,
  `wiki_git_delete`, `wiki_git_search` (grep), all git-shell/filesystem
  based over `<repo>.wiki.git`; dispatched from `cmd_wiki.spl`'s
  `_wiki_github_list/view/edit/create/delete/search` functions.
- `git --backend bitbucket`: **G7**/**G7b** — **Done**, under different
  names than proposed: `bb_repo_view(client, ws, slug)` (not `bb_get_repo`)
  and `bb_list_repos(client, ws, limit)`, both in `adapter_bitbucket.spl`,
  wired at `cmd_bb.spl`'s `repo view`/`repo list`. **G10** `bb_list_prs` —
  **Done**, `adapter_bitbucket.spl:874`, wired at `cmd_bb.spl`'s `pr list`.
  **G12** `pr checkout` — **still open**: `_bb_pr()`'s match arms are only
  `create`/`view`/`list`; no `checkout` case exists for the bitbucket
  backend (unlike the equivalent GitHub `pr checkout` passthrough, which is
  done — see P1).

**Test evidence for this pass:** `bin/simple test test/01_unit/app/devhub/`
→ 25 spec files, 661 tests, 0 failed (2026-07-20).

---

## 8. Sibling documents

- `facade_tasks_git_wiki.md` — command tables + gaps for `task_manager`,
  `git`, `wiki`.
- `facade_storage.md` — command tables + gaps for `web_storage`.
- `facade_email.md` — command tables + gaps for `email`.
