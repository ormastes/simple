# devhub — Usage Guide

Date: 2026-07-20

`devhub` is a single CLI that gives an LLM agent (or a developer) the UX of
several famous tools — `gh`, `mc`, a Gmail client — over whichever real
backend a team actually uses. Instead of learning the Jira REST API, the
Bitbucket API, the MinIO S3 dialect, and Microsoft Graph, you learn `gh`-style
verbs once (`list`, `view`, `create`, `edit`, `comment`, `close`, `search`,
`ls`, `cp`, `mb`, `inbox`, `send`, ...) and `devhub` routes them to the
configured backend, or lets you pick one with `--backend`.

Five facades ship today: `tasks` (Jira + GitHub issues), `github`/`bb` (GitHub
+ Bitbucket, the "git" facade), `wiki` (Confluence + GitHub wiki), `storage`
(MinIO/S3, `mc`-shaped), and `email` (Gmail-semantics over mail-cli + Outlook
Graph). A handful of older, single-backend commands (`jira`, `minio`,
`outlook`, `api`, `auth`, `daily-debug`) also exist directly — see
[Other commands](#other-commands).

Source: `src/app/devhub/` (dispatcher: `main.spl`). Design docs:
`doc/05_design/app/devhub/`.

## Setup

Run it as `bin/devhub <command> [flags]`. `bin/itf` is a permanent compat
alias — both wrapper scripts run the exact same CLI, so any example below
also works with `itf` substituted for `devhub`.

Launch the desktop dashboard with `bin/devhub --gui`. It binds only to
`127.0.0.1` (port `8765` by default) and opens the repo-managed Electron shell.
Use `--browser` to open the system browser instead, or `--port N` to choose a
different unprivileged port. The GUI is a read-only command dashboard;
credentialed backend operations remain explicit terminal commands.
It uses the registered Simple OS `fluid_light` default: the light, macOS-like
liquid-glass package compiled from `config/themes/raw/fluid_os/DESIGN.md`.

Two separate config files, because the email facade predates and outgrew the
original `itf` config format:

| What | Path | Holds |
|---|---|---|
| Main config | `~/.config/itf/config.sdn` | Confluence/Jira URLs, `wiki.default_backend`, `tasks.default_backend`, `tasks.jira_done_status`, editor/pager overrides, `[token_cmd]` section |
| Main auth | `~/.config/itf/auth.sdn` | Per-provider tokens/credentials: `confluence`, `jira`, `bitbucket`, `minio`, `outlook` sections |
| Email config | `~/.config/devhub/email.sdn` | `default_account` + one or more `accounts` blocks (provider, email, `password_cmd`, and Graph tenant/client fields) — see `facade_email.md` §7 |

`devhub auth login`/`status`/`logout` only automates **Confluence and Jira**:

```bash
devhub auth login --confluence --url https://company.atlassian.net/wiki --user you@co.com --token TOKEN
devhub auth login --jira                                              # delegates to `acli jira auth login --web`
devhub auth login --jira --url URL --user EMAIL --token TOKEN         # also wires the REST curl fallback acli lacks
devhub auth status
devhub auth logout --confluence
```

Other backends have no `devhub auth` verb — their credentials go straight
into `auth.sdn`/`email.sdn`, or an external tool's own login:
- **github**: delegates to the system `gh` CLI; run `gh auth login` yourself.
- **bitbucket**: add a `bitbucket: token = <repo access token>` block to
  `auth.sdn` by hand (see the `/repo_and_pull_req:bb:bb_setup` skill).
- **minio**: add a `[minio]` block to `auth.sdn` (`url`, `region`,
  `access_key`, `secret_key`, `tls_skip_verify`).
- **outlook**: add `tenant_id`/`client_id`/`shared_mailbox` under `outlook:`
  in `auth.sdn`; the client secret comes from env var `GRAPH_CLIENT_SECRET`
  (override the env var name with `outlook.client_secret_env`).
- **email**: write `~/.config/devhub/email.sdn` directly — see below.

**Keeping secrets out of plaintext files** — both config files support a
"run a command, use its stdout as the secret" pattern instead of storing the
token at rest:
- Main config `[token_cmd]` section: `jira: pass show jira/api-token` —
  resolved by `resolve_auth_token()` in `config.spl`, which prefers the
  configured command and falls back to the plaintext token in `auth.sdn`.
- Email accounts: each account block has its own `password_cmd` field, e.g.
  `password_cmd: "pass show mail/work-gmail"` (see the shipped example in
  `cmd_email.spl`).

## Facade: `tasks` (alias: `task_manager`) — Jira + GitHub issues

`gh issue`-shaped view over two trackers.

| Verb | Does |
|---|---|
| `list` | List issues (`--assignee`, `--label`, `--state`, `--search`, `--limit`) |
| `view <id>` | View one issue (a bare number → GitHub, `PROJ-123`-shaped → Jira) |
| `create` | Create (`--title`, `--body`, `--project`, `--type`) |
| `comment <id>` | Add a comment (`--body`) |
| `close <id>` | Close |
| `edit <id>` | Edit (`--title`/`--body`/`--status`; GitHub also: `--add-label`, `--remove-label`, `--add-assignee`, `--remove-assignee`, `--milestone`) |
| `search <query>` | Alias for `list --search <query>` |

Shared flags: `--backend jira\|github\|all` (list/search only — single-item
verbs reject `all`), `--assignee` (`@me` supported), `--label`, `--state
open\|closed\|all`, `--search`, `--limit` (default 30), `--json`/`--jq`,
`--web` (opens the GitHub issue in a browser; for Jira only `view` supports
it). Backend precedence: `--backend` flag, else `tasks.default_backend` in
config.sdn, else `github`. For a single-item verb without `--backend`, an id
shaped like `PROJ-123` auto-detects Jira.

```bash
devhub tasks list --assignee @me --state open
devhub tasks view PROJ-123
devhub tasks create --backend jira --project PROJ --title "New bug"
devhub tasks close 42 --backend github
```

Requires: `gh` CLI (github backend) or `acli`/Jira curl credentials (jira
backend).

## Facade: `git` — `gh`/`git` (routing) + `github`, `bb`/`b` (explicit)

`devhub gh` (alias `devhub git`) is **one gh-shaped command that works against
whichever backend this repository is on**. It resolves the backend, then either
passes straight through to the real `gh` (GitHub) or translates gh's flags into
Bitbucket's and normalises Bitbucket's JSON back into gh's field names.

```bash
devhub gh pr create --title T --body B --base main --head work/x
devhub gh pr list --state open --json number,title,headRefName
devhub gh pr merge 42 --squash
```

The two host-specific commands below (`github`, `bb`) still exist and are
unchanged; use them to address one host explicitly.

### Replacing `gh` outright (`bin/gh`)

The reason devhub went unused was mechanical: people and agents type `gh`, and
nothing was in the way. `bin/gh` is a shim that fixes that — put the repo's
`bin/` ahead of the real `gh` on `PATH` and every existing habit, script, and
agent instruction routes through devhub with **no change to what anyone types**:

```bash
export PATH="/path/to/repo/bin:$PATH"
gh pr create --title T --base main --head work/x   # -> devhub, or -> real gh
```

Two properties worth knowing:

- **It is free on GitHub.** The shim resolves the backend in POSIX shell
  (~0.078 s) and, for `github`, `exec`s the real `gh` without entering Simple
  at all — so it is byte-identical to not having a shim. Only a non-GitHub
  backend pays the ~12 s interpreter startup, and only because there is real
  translation to do.
- **It cannot recurse.** devhub's GitHub adapter shells out to `gh`; with the
  shim on `PATH` that would loop forever. The shim resolves the real binary
  first and exports `DEVHUB_REAL_GH`, which the adapter prefers.

Escape hatches: `DEVHUB_GH_PASSTHROUGH=1` forces the real `gh` unconditionally;
`DEVHUB_GIT_BACKEND=<github|bitbucket>` overrides resolution for one command.

### Which backend? (resolution order)

Highest precedence first — the first rung that yields a known backend wins, and
the source is named in errors so a surprising choice is traceable:

| # | Rung | Set it with |
|---|---|---|
| 1 | `--backend` flag | `devhub gh --backend bitbucket pr list` |
| 2 | environment | `DEVHUB_GIT_BACKEND=bitbucket` |
| 3 | repo config (committed, shared) | `.spipe/config.sdn` → `devhub:` → `git_backend:` |
| 4 | user config | `~/.config/itf/config.sdn` → `git:` → `default_backend:` |
| 5 | remote host sniff | an `origin` pointing at `github.com` / `bitbucket.org` |

Nothing resolved is an **error naming every way to fix it**, never a guess.

Bitbucket coordinates resolve on the same shape:
`--workspace`/`--repo` > `BB_WORKSPACE`/`BB_REPO` > `.spipe/config.sdn`
(`bb_workspace`, `bb_repo`) > `~/.config/itf/config.sdn` (`[bitbucket]`).

```sdn
# .spipe/config.sdn — tracked by git, so NAMES of secrets only, never secrets
devhub:
  git_backend: bitbucket
  bb_workspace: acme
  bb_repo: widgets
  bitbucket_token_env: BB_TOKEN
```

Credentials resolve `[token_env]` (read `$NAME` from the environment) >
`[token_cmd]` (run a command, e.g. `pass show ...`) > `auth.sdn` plaintext.

### What translation does and does not do

On a non-GitHub backend, gh flags are renamed (`--head`→`--source`,
`--base`→`--dest`), `--state closed` becomes Bitbucket's `DECLINED`, and
`gh pr merge`/`review --approve`/`comment` are renested onto Bitbucket's
top-level `merge`/`approve`/`comment post`. `--json` output is re-keyed to gh's
names (`number`, `headRefName`, `baseRefName`, `author.login`, `url`, `body`,
`isDraft`).

**A gh flag with no backend equivalent is refused by name, never dropped**
(`--draft`, `--fill`, `--web`, `--template`, `--admin`, `--auto`, `--search`).
A silently-dropped `--base` would open a PR against the wrong branch and still
exit 0; a refusal is strictly safer than an approximation.

### `github` (alias `gh` when routed — see above)

Thin wrapper around the real `gh` CLI: `list` gets reformatted into a table
(or `--json`/`--jq`); every other verb is a **verbatim passthrough** to `gh`
(all remaining flags go straight through, uninterpreted).

| Verb | Passthrough target |
|---|---|
| `issue list\|view\|create\|edit\|comment\|close` | `gh issue ...` |
| `pr list\|view\|create\|merge\|review\|checkout` | `gh pr ...` |
| `repo view\|clone` | `gh repo ...` |

```bash
devhub github issue list --state open --limit 20
devhub github issue edit 123 --add-label bug
devhub github pr create --title T --body B --base main
devhub github pr merge 42 --squash
devhub github pr review 42 --approve
devhub github repo clone owner/name
```

Requires: `gh` installed and authenticated.

### `bb` (alias `b`) — Bitbucket Cloud

Real REST client (`adapter_bitbucket_curl.spl`), not a passthrough — requires
`--workspace`/`BB_WORKSPACE`, `--repo`/`BB_REPO`, and a `bitbucket.token` in
`auth.sdn`.

| Verb | Flags |
|---|---|
| `repo list\|view` | `--workspace`, `--limit` |
| `pr create` | `--title`, `--source`, `--dest`, repeatable `--reviewer UUID` |
| `pr view <id>` / `pr list` | `--state open\|merged\|declined\|all`, `--limit` |
| `comment list\|post <PR_ID>` | `post`: `--content`, `--inline-path`, `--inline-to`, `--inline-from` |
| `approve <PR_ID>` | `--unapprove` (default action is approve) |
| `merge <PR_ID>` | `--strategy`, `--keep-source` |
| `status <PR_ID>` | `--ready-check` |

List commands (`pr list`, `repo list`) page up to a **10-page hard cap**; a
result set that hits the cap prints a truncation note and — in `--json` —
sets `_capped: true`.

```bash
devhub bb pr create --title "Fix login" --source feature/x --dest main --reviewer <uuid>
devhub bb pr list --state open --limit 50
devhub bb approve 42
devhub bb merge 42 --strategy squash
```

## Facade: `wiki` — Confluence + GitHub wiki

| Verb | Does |
|---|---|
| `list`/`ls` | List pages in a space |
| `view` | View a page |
| `edit` | Edit a page in `$EDITOR` |
| `create` | Create a page |
| `delete`/`rm` | Delete a page |
| `search` | Search pages by title |

Flags: `--backend confluence\|github` (precedence: flag > `wiki.default_backend`
in config.sdn > `confluence`), `--space KEY` (Confluence), `--repo`/`-R
OWNER/NAME` (GitHub — the repo whose `.wiki.git` to use), `--json`/`--jq`,
`--web`, `--limit N` (default 25, Confluence only), `--push` (GitHub backend
only — pushes local wiki-git commits back to GitHub; never implied).

```bash
devhub wiki list --space ENG
devhub wiki view 12345 --json id,title
devhub wiki edit 12345 --message "fix typo"
devhub wiki list --backend github --repo acme/widgets
devhub wiki view Home --backend github --repo acme/widgets
```

## Facade: `storage` (alias `web_storage`) — `mc`-style S3/MinIO

Addressing is `alias/bucket[/key...]` or a local filesystem path; direction
for `cp`/`mirror` is inferred from which side is local vs. `alias/...`. Only
one alias exists today: bare `minio` (single-endpoint fallback onto the
`[minio]` section in `auth.sdn`).

| Verb | Does |
|---|---|
| `ls [alias[/bucket[/prefix]]]` | List buckets, or objects under a bucket/prefix |
| `cp SRC DST` | Copy (upload or download) |
| `cat alias/bucket/key` | Print object body (`--range R`) |
| `stat alias/bucket/key` | Size/etag/last-modified |
| `mb` / `rb alias/bucket` | Create / delete a bucket (`rb --force`: empty it first, capped at 1000 objects) |
| `rm alias/bucket/key` | Delete an object (`-r`/`--recursive`: delete a whole prefix, capped at 1000 objects) |
| `presign` / `presign-put` | Presigned GET / PUT URL (`--expires SECONDS`) |
| `du alias/bucket[/prefix]` | Aggregate sizes under a prefix (`--depth N`) |
| `mirror SRC DST` | Sync a local dir <-> bucket/prefix (`--dry-run`, `--remove`) |
| `health [alias]` | Probe `/minio/health/live` |

Other flags: `--json`, `--bytes` (raw byte counts), `--content-type` (for
`cp` upload), `--no-pager`.

```bash
devhub storage ls minio/my-bucket/logs/
devhub storage cp ./report.json minio/my-bucket/reports/report.json
devhub storage cat minio/my-bucket/config.yaml
devhub storage mirror ./dist minio/my-bucket/dist --dry-run
devhub storage presign minio/my-bucket/report.json --expires 3600
```

## Facade: `email` — Gmail semantics over mail-cli + Outlook Graph

| Verb | Does |
|---|---|
| `inbox` | `--unread`, `--threads`, `--label L`, `--limit N`, `--json` |
| `read <id>` | `--raw`, `--folder F` |
| `send` | `--to`, `--cc`, `--bcc`, `--subject`, `--body` or `--input FILE`, repeatable `--attach` |
| `reply <id>` | `--body`/`--input`, `--all` |
| `forward <id>` | `--to`, `--body` |
| `search "<query>"` | `--limit N`, `--json` |
| `label <id>` | repeatable `--add L`, repeatable `--remove L` |
| `star <id>` | `--off` to unstar |
| `archive <id>` | — |
| `draft list\|create\|send <id>` | `create`: `--to`, `--subject`, `--body` |

Common flag: `--account NAME` (selects an account from `email.sdn`; default
account is used otherwise).

Per-account `provider` picks the backend:

| Provider | Backend | Coverage |
|---|---|---|
| `gmail` | mail-cli (IMAP/SMTP) | full parity — every verb above |
| `outlook_imap` | mail-cli (IMAP/SMTP) | full parity |
| `outlook` | Microsoft Graph adapter | `inbox`/`read`/`archive` only — `search`/`send`/`reply`/`forward`/`label`/`star`/`draft` return an explicit gap error naming the missing Graph function, not a silent failure |

```bash
devhub email inbox --unread --limit 20
devhub email read 42 --account work-gmail
devhub email send --to a@b.com --subject "status" --body "all green"
devhub email search "from:alice subject:invoice is:unread"
devhub email label 42 --add important --remove unread
```

## Backend-native search syntax

Search strings are passed to the backend **untranslated** — you write the
backend's own query language, not a devhub-invented DSL:
- `tasks --search` / `jira search`: a Jira JQL fragment.
- `github issue|pr list`: `gh`'s own search qualifiers (passed straight
  through to `gh ... list`).
- `bb`: no free-text search verb today (list + filters only).

The one exception is `email search`, where Gmail-style query operators
(`from:`, `subject:`, `is:unread`, ...) are translated per backend: passed
verbatim to Gmail's `X-GM-RAW` IMAP extension for `gmail`/`outlook_imap`
mail-cli backends, and to Graph `$search`/`$filter` for the `outlook`
backend. See `doc/05_design/app/devhub/facade_email.md` §5 for the full
per-operator translation table and the operators that have no equivalent on
a given backend.

## Shared flags

These work the same way across facades (implemented once in `output.spl`/
`flags.spl`):

| Flag | Effect |
|---|---|
| `--json [FIELDS]` | JSON output, optionally restricted to a comma-separated field list |
| `--jq EXPR` | Filter JSON output (e.g. `.[].title`) |
| `--web` | Open the item in a browser (supported per-verb — see each facade above) |
| `--no-pager` | Never page long listing output (storage `ls`, github `list`, bb list commands) |
| `--help` / `-h` | Per-command help |

Global log/output flags (from `std.cli.log_modes`, valid as a prefix before
the subcommand): `--log-mode <human\|llm\|json>`, `--human`/`--llm`/`--json`
shorthand, `--stdout`/`--tui` (output surface), `--progress
<summary\|count\|dot\|none>`, `--dots`/`--count`/`--no-progress`,
`--quiet`/`--verbose`.

Color respects `NO_COLOR` (disables) and `ITF_FORCE_COLOR=1` (forces). Editor
resolution order: `ITF_EDITOR` > `GH_EDITOR` > `EDITOR` > `VISUAL` > `vi`.
Pager: `ITF_PAGER` env var, else `PAGER`.

## Other commands

Older, single-backend commands that predate the facades and still work
directly (no `--backend` selection — each talks to exactly one system):

| Command | Talks to | Notable verbs |
|---|---|---|
| `jira` (alias `j`) | Jira only | `view`, `search` (JQL), `create`, `update`, `comment`, `transition` — `update`/`comment`/`transition` try `acli` first, then fall back to REST v3 curl if `jira.url`+`jira.email`+a token are configured |
| `minio` (alias `mio`) | MinIO/S3 only | `ls`, `get`, `put`, `stat`, `mb`, `rb`, `rm`, `presign`, `presign-put`, `health` |
| `outlook` (alias `ol`) | Microsoft Graph only | `folders`, `messages <FID>`, `get <MID>`, `move <MID> --to F`, `mark <MID>` |
| `api` | Raw REST | `api <GET\|POST\|PUT\|DELETE> <URL/path>` against Confluence (default) or Jira (`--jira`) — like `gh api` |
| `daily-debug` (alias `dd`) | mail → jira → minio | 7-step pipeline: reads inbox since a saved watermark, extracts Jira keys + MinIO URLs, triages artifacts, writes a daily digest, advances the watermark (`--quiet`, `--dry-run`) |

## Known limits

Honest, currently-open gaps — do not expect these to work:

- **Non-tty color leak**: `should_use_color()` has no real `isatty` check
  (`rt_is_tty` extern doesn't exist yet), so piped/redirected output still
  gets ANSI color codes unless you set `NO_COLOR=1` explicitly (bug
  `itf-color-nontty-gap`).
- **`storage ls -r`/`--recursive` is a no-op**: listing is *always* fully
  recursive today; there is no folder-collapsed non-recursive mode yet
  (prints a note saying so). See `facade_storage.md` §3.
- **`storage`/`minio` binary upload**: `cp`/`put` read real file bytes but
  the underlying transport can't push arbitrary binary bodies reliably for
  all content types — use `presign-put` (generate a presigned PUT URL, then
  upload with a real HTTP client) as the documented workaround.
- **`storage mirror` compares size only**, not mtime — a same-size, changed
  file will not be re-copied.
- **`rm --recursive`/`rb --force`/`mirror --remove`** are all capped at 1000
  objects per side (no batch `DeleteObjects` call in the adapter); over the
  cap, they refuse and point you at the real `mc` CLI.
- **`bb`**: no free-text search verb; list endpoints cap at 10 pages
  (`_capped:true` in `--json` past the cap).
- **`gh` facade covers `pr` and `repo` only** on non-GitHub backends. `issue`
  is not routed (Bitbucket issues are a different product from Jira, which the
  `tasks` facade already covers). On the `github` backend everything works,
  because it is a passthrough.
- **`gh --json` is gh-shaped for PR objects only.** `pr view/list/create/merge`
  are re-keyed to gh's field names; `approve`/`comment`/`status` still emit
  backend-native JSON. gh's own JSON for those is minimal and nothing here
  parses it.
- **No `bin/mc` or `bin/jira` shim yet.** The same interception pattern applies
  to the `storage` and `tasks` facades, which are already mc- and gh-shaped.
  Only `gh` is shimmed, because that is where the demonstrated bypass was.
- **`bin/gh` is opt-in.** Nothing puts `bin/` on `PATH` for you. On a GitHub
  repo installing it changes no behaviour (it `exec`s the real `gh`); it earns
  its keep when the backend is not GitHub.
- **`email` on the `outlook` (Graph) provider**: only `inbox`/`read`/`archive`
  work; `search`/`send`/`reply`/`forward`/`label`/`star`/`draft` return an
  explicit gap error rather than running. Use `outlook_imap` (mail-cli) for
  full parity against the same mailbox.
- **`.split(sep, N)` limit is ignored by the currently-deployed seed
  interpreter** (`text-split-limit-ignored`) — irrelevant to devhub users
  directly, but it's why `config.spl`'s SDN parser deliberately finds only
  the *first* colon instead of using `.split(":", 2)` (a value containing
  its own colon, like a URL, would otherwise truncate).
- **CLI banner still says "itf"**: `devhub --help`/`--version` print
  `itf`-branded text (`itf — gh-like CLI for Jira + Confluence`,
  `Config: ~/.config/itf/config.sdn`) — cosmetic only, verified by running
  `bin/devhub --help` directly; functionality is unaffected.
- **Top-level `--help` is incomplete**: `devhub --help` only lists
  `wiki, jira, api, auth, bb, minio, outlook, github, daily-debug` — it omits
  `storage`/`web_storage`, `email`, and `tasks`/`task_manager` even though all
  three dispatch and work (see `main.spl`'s `handle_itf` match block). Use
  `devhub <facade> --help` for the real per-facade help.

## Related

- Design overview: `doc/05_design/app/devhub/devhub_overview.md`
- Facade specs: `doc/05_design/app/devhub/facade_tasks_git_wiki.md`,
  `facade_storage.md`, `facade_email.md`
- Source: `src/app/devhub/` (dispatcher `main.spl`, one `cmd_*.spl` per
  facade/command, adapters in `adapter_*.spl`)
- Specs: `test/01_unit/app/devhub/`
