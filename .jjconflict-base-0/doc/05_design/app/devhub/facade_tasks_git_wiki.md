# devhub facades — `task_manager` (`tasks`), `git`, `wiki`

Condensed from gh-CLI ground truth (`gh --help` tree, v2.45.0, help-only
capture, no network calls) plus a read of `src/app/itf/{cmd_github,cmd_jira,
cmd_bb,cmd_wiki}.spl` and their adapters. See `devhub_overview.md` for D1–D8
cross-cutting rules (backend precedence, `@me`, search-string handling,
state mapping, `--backend all` semantics, noun-verb rules) referenced by
column below.

**Key structural fact:** gh has no `wiki` command at all — GitHub wikis are a
separate `<repo>.wiki.git` git repository, not a REST/GraphQL surface. This is
the headline gap for the `wiki` facade (§3).

---

## 1. gh universal conventions (apply across every noun)

| Convention | Detail |
|---|---|
| `-R, --repo [HOST/]OWNER/REPO` | Inherited flag on every noun-scoped command; selects repo without `cd`. |
| Entity reference | number (`123`), URL, or (PR only) branch name (`patch-1`, `OWNER:patch-1`) — positional, no flag. |
| `--json fields` | Switches to JSON; `fields` required comma-list (no bare `--json`). |
| `-q, --jq expression` | jq-filters the `--json` output. |
| `-t, --template string` | Go-template formats the `--json` output. |
| `-w, --web` | Opens the equivalent web page instead of doing the operation locally. |
| `-L, --limit int` | Default 30, on every `list`/`search`. |
| `-s, --state string` | `{open\|closed\|all}` on issue list, `{open\|closed\|merged\|all}` on pr list. |
| `-l, --label strings` | Repeatable, AND-filter. |
| `-a, --assignee` / `-A, --author` | Free string; `"@me"` is a recognized literal for the authenticated user (D3). |
| `-S, --search query` | On `list`: raw GitHub search-qualifier string layered on structured flags (D2). |
| `--app string` | Filter by bot/App author (issue/pr list, search issues/prs). |
| ALIASES | `new` on `issue create`/`pr create`; `ls` on `issue list`/`pr list`/`repo list`/`label list`. |
| Body input | `-b/--body`, `-F/--body-file file` (`-` = stdin) — issue/pr create, comment, merge, review. |
| `--recover string` | issue/pr create only — resumes a failed create using cached draft input. |

---

## 2. `devhub task_manager` (alias `tasks`) — Jira + GitHub issues

Backends: `github` → `adapter_github.gh_run` (issue passthrough, per
`cmd_github.spl`); `jira` → `adapter_jira.spl` / `adapter_jira_curl.spl`.

| devhub command | Synopsis | Flags | Backend mapping | Output columns | Adapter fn / gap |
|---|---|---|---|---|---|
| `tasks list` | `devhub tasks list [flags]` | `--backend` `-a/--assignee` (`@me`) `-A/--author` `-l/--label` `-s/--state {open\|closed\|all}` `-S/--search` `-L/--limit` `--json` `--jq` `-w/--web` | github: `gh_run(["issue","list",...])` (= `_github_list("issue",...)`). jira: **gap G1** — needs `jira_build_list_jql(...)` to synthesize JQL from flags, then `jira_search(config, jql, fields, limit)`. `all`: run both, union (D6). | `BACKEND`\* `KEY/NUMBER` `STATE` `ASSIGNEE` `SUMMARY/TITLE` `UPDATED` | github: existing `_github_list`. jira: existing `jira_search` + new `jira_build_list_jql` (G1). \*`BACKEND` col only when `--backend all`. |
| `tasks view <id>` | `devhub tasks view {<number>\|<KEY>\|<url>} [flags]` | `-c/--comments` `--json` `--jq` `-w/--web` | github: `gh_run(["issue","view",id,...])`. jira: `jira_view_issue(config, key)`. Backend auto-detected from id shape (`\d+` → last-used/default backend; `PROJ-123` → jira) when `--backend` omitted. | n/a (detail view) | github: existing `_github_passthrough`. jira: existing `jira_view_issue`. |
| `tasks create` | `devhub tasks create [flags]` | `-t/--title` `-b/--body` `-F/--body-file` `-a/--assignee` (`@me`) `-l/--label` `-m/--milestone` `--project` (jira project key; gh's `-p/--project` = GH Projects board — **resolve collision**: use `--project` for jira project key and a distinct `--gh-project` for GH Projects board, documented as a deliberate deviation from gh) | github: `gh_run(["issue","create",...])`. jira: `jira_create_issue(config, project, summary, type, description)` — needs `--type` too (Task/Bug/Story), already supported by adapter. | Success line + key/number | github: existing passthrough. jira: existing `jira_create_issue`. |
| `tasks comment <id>` | `devhub tasks comment <id> [flags]` | `-b/--body` `-F/--body-file` | github: `gh_run(["issue","comment",...])`. jira: `jira_add_comment` (acli) → `jira_curl_add_comment` fallback, exactly as `_jira_comment` today. | success line | Both exist, reuse verbatim. |
| `tasks close <id>` | `devhub tasks close <id> [flags]` | `-c/--comment` `-r/--reason {completed\|not planned}` | github: `gh_run(["issue","close",...])`. jira: `jira_transition_issue(config, key, tasks.jira_done_status)` (D5) — `-r/--reason` has no jira equivalent, ignored with `print_warning` for jira backend. | success line | github: already wired via `_github_passthrough(["issue","close",...])` — no gap. jira: existing `jira_transition_issue`, needs D5's configured done-status. |
| `tasks edit <id>` | `devhub tasks edit <id> [flags]` | `--add-label`/`--remove-label` `--add-assignee`/`--remove-assignee` (`@me`) `-b/--body` `-t/--title` `-m/--milestone` `--status X` (jira-only, transition) | github: **gap G5** — no existing `edit` wiring, add `_github_passthrough(["issue","edit",...])`, trivial one match arm. jira: body/title → `jira_update_issue`; `--status` → `jira_transition_issue`; label/assignee add/remove → **gap G1b**, `adapter_jira.spl` has no label/assignee mutation fn today (needs a source check of `acli` capability, unscoped). | success line | Mixed: some exist, some gaps (G1b, G5). |
| `tasks search <query>` | `devhub tasks search <query\|JQL> [flags]` | Same filter flags as `list`, query positional | Thin alias for `tasks list --search <query>` (D2), kept as a **separate verb** (existing entry point `itf jira search <JQL>`; gh itself keeps both `gh issue list --search` and `gh search issues`). | Same as `list` | github: `gh_run(["issue","list","--search",query,...])` — thin wrapper, no new fn. jira: existing `jira_search(config, jql, fields, limit)` used directly (raw JQL, no G1 synthesis needed — query already backend-native). |

\* **G1** (Jira list-via-JQL-synthesis) is the single highest-value new
adapter function — separates "jira has search" from "jira has list,
filterable exactly like gh." `tasks search` does not need G1 (query already
raw JQL, matching today's `jira search`).

---

## 3. `devhub git` — GitHub + Bitbucket repos/PRs

Backends: `github` → `adapter_github.gh_run` (repo/pr passthrough);
`bitbucket` → `adapter_bitbucket.spl`/`_curl` twin. **No `--backend all` for
`git`** — a repo lives in exactly one place by construction, unlike
issues/pages which can be duplicated. `--backend` selects which single
backend a repo/PR reference belongs to, not a fan-out.

| devhub command | Synopsis | Flags | Backend mapping | Output columns | Adapter fn / gap |
|---|---|---|---|---|---|
| `git repo view [repo]` | `devhub git repo view [name] [flags]` | `-b/--branch` `--json` `--jq` `-w/--web` | github: `gh_run(["repo","view",...])`, existing (`_github_repo`'s `view` case already wired). bitbucket: **gap G7** — no adapter fn at all (`adapter_bitbucket.spl` is PR-only); needs new `bb_get_repo(client, ws, repo)` hitting `GET /2.0/repositories/{ws}/{repo}`. | description/README-ish detail dump | github: existing passthrough. bitbucket: gap G7. |
| `git repo list [owner]` | `devhub git repo list [owner] [flags]` | `--archived`/`--no-archived` `--fork`/`--source` `-l/--language` `--topic` `--visibility` `-L/--limit` `--json` `--jq` | github: **gap G8** — `_github_repo` only wires `view`, no `list` case; trivial fix, add `"list": _github_list("repo", rest)`. bitbucket: **gap G7b** — needs `bb_list_repos(client, ws)` (`GET /2.0/repositories/{ws}`), no such fn exists. | `BACKEND`(if combined)/`NAME` `DESCRIPTION` `VISIBILITY` `UPDATED` | Both gaps (G8, G7b). |
| `git repo clone <repo> [dir]` | `devhub git repo clone <repo> [dir] [-- gitflags]` | `-u/--upstream-remote-name` | github: `gh_run(["repo","clone",...])` — **gap G9**, not wired in `cmd_github.spl` (`_github_repo` only has `view`), trivial passthrough add. bitbucket: plain `git clone https://bitbucket.org/{ws}/{repo}.git [dir]` — no API adapter needed, shell to `git clone` directly. | n/a | github: gap G9 (trivial). bitbucket: no adapter fn needed. |
| `git pr list` | `devhub git pr list [flags]` | `-a/--assignee` `-A/--author` `-B/--base` `-H/--head` `-d/--draft` `-l/--label` `-s/--state {open\|closed\|merged\|all}` `-S/--search` `-L/--limit` `--json` `--jq` `-w/--web` | github: existing `_github_list("pr",...)`. bitbucket: **gap G10** — no list fn exists; `adapter_bitbucket.spl` only has get/create/comment/approve/merge/status for a *known* PR id, nothing hits `GET /2.0/repositories/{ws}/{repo}/pullrequests`. Single biggest bitbucket-side gap: needs new `bb_list_prs(client, ws, repo, state) -> (bool, [BbPr], text)`. | `BACKEND` `NUMBER` `TITLE` `STATE` `AUTHOR` `BRANCH` `UPDATED` | github: exists. bitbucket: gap G10 (net-new). |
| `git pr view <id>` | `devhub git pr view [<number>\|<url>\|<branch>] [flags]` | `-c/--comments` `--json` `--jq` `-w/--web` | github: existing passthrough. bitbucket: existing `bb_get_pr` (+ `bb_list_pr_comments` for `-c`), via `cmd_bb.spl`'s `_bb_pr_view`. | detail view | Both exist. |
| `git pr create` | `devhub git pr create [flags]` | `-B/--base` `-b/--body` `-F/--body-file` `-d/--draft` `-f/--fill` `-H/--head` `-l/--label` `-r/--reviewer` `-t/--title` `--no-maintainer-edit` | github: **gap G11** — `_github_pr`'s match arms are list/view/merge/checkout only, no `create`; trivial add, gh supports it natively. bitbucket: `bb_create_pr(client, ws, repo, title, source, dest, reviewers)` — existing via `_bb_pr_create`; **no `--fill`/`-f` equivalent** (Bitbucket adapter has no commit-log title/body derivation) — documented gap, not fixable without new local-git-log-reading logic. | success line + PR id/url | github: gap G11 (trivial). bitbucket: exists minus `--fill`. |
| `git pr merge <id>` | `devhub git pr merge [<number>\|<url>\|<branch>] [flags]` | `-m/--merge` `-r/--rebase` `-s/--squash` `-d/--delete-branch` `--admin` `--auto` `-b/--body` `-F/--body-file` | github: existing passthrough. bitbucket: `bb_merge_pr(client, ws, repo, id, strategy, close_source_branch)` via `_bb_merge` — strategy string differs from gh's flag-per-strategy; devhub normalizes `-s/--squash`→`"squash"`, `-m/--merge`→`"merge_commit"`, `-r/--rebase`→`"fast_forward"` at the CLI layer, no adapter change needed. `--admin`/`--auto`/`--match-head-commit` have no Bitbucket REST equivalent — unsupported, error clearly rather than silently ignore. | success line + merge commit | Both exist; strategy-name mapping is CLI-layer glue only. |
| `git pr checkout <id>` | `devhub git pr checkout {<number>\|<url>\|<branch>} [flags]` | `-b/--branch` `--detach` `-f/--force` `--recurse-submodules` | github: existing `_github_passthrough`. bitbucket: **gap G12** — no adapter support; needs `git fetch` of the PR's source branch (`bb_get_pr` already returns `source_branch`) then plain `git checkout -b <local> <remote>/<source_branch>` — CLI-layer git shell-out, not a REST adapter fn. | n/a | github: exists. bitbucket: gap G12 (git-shell composition). |
| `git pr review <id>` | `devhub git pr review [<number>\|<url>\|<branch>] [flags]` | `-a/--approve` `-b/--body` `-F/--body-file` `-c/--comment` `-r/--request-changes` | github: **gap G13** — `_github_pr` has no `review` case. bitbucket: `-a/--approve`→`bb_approve_pr`, plain comment→`bb_post_pr_comment`, both exist via `_bb_approve`/`_bb_comment_post`; `-r/--request-changes` has **no Bitbucket REST equivalent** (no "request changes" review state distinct from a comment) — document as unsupported; recommend erroring, not faking semantics with a `[Requesting changes]`-prefixed comment. | success line | github: gap G13 (trivial passthrough add). bitbucket: mostly exists, one semantic gap. |

---

## 4. `devhub wiki` — Confluence + GitHub wiki

Backends: `confluence` → `adapter_confluence.spl`, ~1:1 with existing
`cmd_wiki.spl`. `github` → **no adapter exists**; GH wikis are a plain git
repo at `github.com/OWNER/REPO.wiki.git`, one markdown/asciidoc file per page,
no REST/GraphQL CRUD API. This is the facade's headline structural gap.

| devhub command | Synopsis | Flags | Backend mapping | Output columns | Adapter fn / gap |
|---|---|---|---|---|---|
| `wiki list` (`ls`) | `devhub wiki list [flags]` | `--space`/`-R` (D8) `-L/--limit` `--json` `--jq` `-w/--web` | confluence: `confluence_list_pages(config, space_id, limit)` — existing, `_wiki_list` verbatim. github: **gap G14** — clone/pull `<repo>.wiki.git` into a local cache dir, `ls` its `*.md`/`*.adoc` files; no REST call, a filesystem operation over a git clone. Needs new `github_wiki_clone_or_pull(repo) -> local_path` git-shell helper. | `ID` `TITLE` `STATUS` `MODIFIED` (confluence); github: `PAGE` `MODIFIED` (file mtime/git log) | confluence: exists. github: gap G14 (git-shell, no REST). |
| `wiki view <page>` | `devhub wiki view <page-id\|page-name> [flags]` | `--format markdown\|storage` `--json` `--jq` `-w/--web` | confluence: `confluence_get_page(config, page_id)`, existing. github: read the cloned `<page-name>.md` file directly — shares G14's clone/pull dependency. | detail dump | confluence: exists. github: gap (shares G14). |
| `wiki create` | `devhub wiki create --space KEY --title T [flags]` (confluence); `devhub wiki create --title T --backend github [flags]` | `--space`/`-R` `-t/--title` `--parent` `--from-file` | confluence: `confluence_create_page`, existing `_wiki_create`. github: create `<title>.md` in the cloned wiki repo, `git add && commit && push` — **gap G15**, pure git-shell composition, no REST call exists for this on GitHub's side at all. | success line + id/url | confluence: exists. github: gap G15 (git-shell). |
| `wiki edit <page>` | `devhub wiki edit <page-id\|page-name> [flags]` | `--message MSG` `--mode markdown\|storage` | confluence: `confluence_update_page` via `$EDITOR` round-trip, existing `_wiki_edit`. github: open the cloned file in `$EDITOR`, `git commit && push` on change — **gap G15b**, shares G14/G15's git-shell layer, reuses `_resolve_editor` from `cmd_wiki.spl` unchanged. | success line | confluence: exists. github: gap (git-shell, reuses existing editor-resolution helper). |
| `wiki delete` (`rm`) | `devhub wiki delete <page-id> [--yes]` | `--yes` | confluence: `confluence_delete_page`, existing `_wiki_delete`. github: `git rm <file> && commit && push` — gap, same git-shell family as G14/G15. | success line | confluence: exists. github: gap. |
| `wiki search <query>` | `devhub wiki search <query> [flags]` | `--space`/`-R` `-L/--limit` `--json` `--jq` | confluence: `confluence_search_pages`, existing `_wiki_search`. github: **gap G16** — `grep`/full-text scan over the cloned wiki repo's files (no server-side search API); simplest correct impl. | `ID` `TITLE` `SPACE` `STATUS` (confluence); `PAGE` `MATCH LINE` (github) | confluence: exists. github: gap G16 (local grep, no REST). |

**`--backend github` scoping recommendation:** treat the whole backend as
"git-repo-of-markdown-files," not "REST resource" — G14–G16 are the *same*
underlying primitive (clone-once, operate on local files, commit+push on
write), not five separate integration problems. Scope as one new module,
`adapter_github_wiki.spl`, with `clone_or_sync(repo) -> path`, `list_pages`,
`read_page`, `write_page`, `delete_page`, `grep_pages` — no new REST client,
only `git` + filesystem shelling (matches `adapter_github.spl`'s existing
pattern of shelling to the `gh`/`git` binary rather than hand-rolling REST).

---

## 5. Gap summary (net-new work, ranked)

| Gap | Facade | Size | What's needed |
|---|---|---|---|
| **G1** | tasks | Medium | `jira_build_list_jql(assignee, label, state, milestone, search) -> text` — JQL synthesizer making `tasks list --backend jira` flag-compatible with `tasks list --backend github`. Highest value: unblocks D2–D4 all at once. |
| **G10** | git | Medium | `bb_list_prs(client, ws, repo, state) -> (bool, [BbPr], text)` — Bitbucket has zero PR-listing today; single biggest bitbucket-side hole. |
| **G7/G7b** | git | Medium | `bb_get_repo` / `bb_list_repos` — Bitbucket adapter is 100% PR-scoped, no repo-level fns at all. |
| **G14–G16** | wiki | Large (one module) | `adapter_github_wiki.spl` — clone/pull/list/read/write/delete/grep over `<repo>.wiki.git`. No REST API exists on GitHub's side; must be git-shell based, same pattern as `adapter_github.spl`. |
| **G5, G9, G11, G13** | tasks/git | Trivial (4 one-line match-arm additions) | `cmd_github.spl` is missing `issue edit`, `repo clone`, `pr create`, `pr review` cases even though the underlying `gh` binary already supports all four — pure passthrough wiring, no adapter logic needed. |
| **G4** (recheck) | tasks | None | Re-verified: `_github_issue`'s `close` case already exists in `cmd_github.spl`. Not a gap. |
| **G1b** | tasks | Unscoped | Jira label/assignee add/remove via `edit` — needs a source check of what `acli jira workitem` supports beyond this doc's read; flag as "needs research," not designed blind. |
| **G6** | all three | Small | New `ItfConfig` fields: `tasks.default_backend`, `git.default_backend`, `wiki.default_backend`, `tasks.jira_done_status` (default `"Done"`), plus Bitbucket workspace/repo config defaults (today only env-var/flag, no config-file default, inconsistent with Jira/Confluence). |
| **G12** | git | Small | Bitbucket `pr checkout` — git-shell composition (`git fetch` + `git checkout -b`) using data `bb_get_pr` already returns; not a REST gap, a CLI-layer omission. |

---

## 6. Error cases (apply across all three facades)

- **Backend unconfigured**: mirrors existing exit code 4 pattern
  (`_require_confluence_auth`/`check_jira_auth`) — "X not configured. Run:
  `devhub auth login --X`."
- **`gh` missing/unauthed**: reuse `gh_available()`/`gh_actionable_error()`
  verbatim (already actionable-error-shaped).
- **Ambiguous backend, no default configured, no `--backend` flag**: error
  listing which backends *are* configured, don't guess.
- **`--backend all` partial failure**: per D6, never hard-fail — print
  successful backend(s)' data + a warning per failed backend, exit 0 if ≥1
  succeeded.
- **Bitbucket-unsupported semantics** (G13's `--request-changes`, merge's
  `--admin`/`--auto`): fail loudly and specifically ("Bitbucket has no REST
  equivalent for --request-changes; use --comment instead") rather than
  silently downgrading semantics.
