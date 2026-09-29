# devhub as a CLI wrapper: forwarding, normalization, and config

**Date:** 2026-09-06
**Scope:** why `devhub` is bypassed today, which CLI grammar each area should
imitate, how to intercept the real CLI, how to translate LLM-shaped input into
a non-GitHub backend and translate its output back into the shape an LLM
expects, and where backend/credential configuration lives.

**Sibling docs:** `doc/05_design/app/devhub/devhub_overview.md` (facade matrix,
decisions D1–D8), `doc/07_guide/app/devhub.md` (user guide).

---

## 0. The problem, stated precisely

`devhub` has 41 source files and ~14.6k lines of working adapters (GitHub via
`gh`, Bitbucket via native REST 2.0, Jira, Confluence, Outlook Graph, MinIO
SigV4). It is nonetheless **not used** for the single most frequent developer
operation in this repo — opening a pull request. `.claude/rules/vcs.md` tells
every agent session to run `gh pr create` directly, and they do.

The reason is mechanical, not cultural. Three findings, each verified in
source on 2026-09-06:

1. **There is no backend-neutral git command.** `devhub github` is a *pure
   passthrough to the system `gh` binary* (`adapter_github.spl:32`,
   `process_run("gh", args)`); `devhub bb` is a separate command with a
   different flag vocabulary (`--source`/`--dest` rather than gh's
   `--head`/`--base`). Nothing reads a configured backend and routes. The
   design doc names this itself under D1: *"`git.default_backend` does not
   exist yet."* So even an agent that wanted to use devhub would have to know
   which backend the repo is on and pick the right subcommand by hand — which
   is exactly the knowledge a wrapper is supposed to remove.
2. **Using devhub is strictly more typing than not using it.** `devhub gh pr
   create` is longer than `gh pr create` and, for a GitHub repo, does
   nothing extra. A wrapper that costs more and adds nothing loses every time.
3. **Nothing intercepts.** `gh` is on `PATH`; devhub is not in the way. An
   instruction in a rules file is the weakest possible enforcement surface —
   this repo has learned the same lesson about pre-push guards
   (`.claude/rules/vcs.md`, "Wiring surface").

The fix therefore has to make devhub **the thing that runs when you type
`gh`**, not a thing you must remember to type instead.

---

## 1. Most-used CLI per area (what grammar to imitate)

The design goal is that a user or an LLM driving devhub feels like it is
driving the tool it already knows. That requires picking, per area, the tool
with the strongest grammar gravity — not the best tool, the *most imitated* one.

| Area | Dominant CLI | Grammar gravity | Devhub facade |
|---|---|---|---|
| **Git hosting / PR review** | **`gh`** (GitHub CLI) | **Decisive.** GitLab's `glab` is an explicit gh-grammar clone (`glab mr create`, same noun-verb, same `--json`); Gitea's `tea` likewise. Bitbucket has **no** maintained official CLI at all — the old `bitbucket-cli` and `ash` are abandoned, and Atlassian's current answer is `acli`, which covers Jira/Confluence far better than repos. So for Bitbucket there is no native grammar to compete with gh's. | `git` (this doc's subject) |
| **Issue tracking** | `gh issue`, then `jira-cli` (`ankitpokhrel/jira-cli`) | `gh issue`'s `list/view/create/edit/close` is the shape people expect. Atlassian's own `acli` is newer and much less known. | `task_manager` / `tasks` — **already gh-shaped** |
| **Object storage** | **`mc`** (MinIO client), then `aws s3` | `mc`'s `ls/cp/cat/stat/mirror/rm/mb` verb set is near-universal for S3-compatible stores; `aws s3` mirrors the same verbs. | `web_storage` / `storage` — **already mc-shaped** |
| **Version control** | `git` | Universal. jj is this repo's choice but `git` is the grammar everyone and every LLM knows. | (out of devhub scope; `bin/sj` covers jj) |
| **Email** | **none dominant** | `mutt`/`neomutt`/`himalaya` are all niche; there is no CLI an LLM can be assumed to know. The strongest shared vocabulary is the **Gmail web UI's** (inbox, thread, label, archive, search operators like `from:`/`is:unread`). | `email` — Gmail-vocabulary, correct call |
| **Wiki / docs** | **none dominant** | `gh` has no wiki verb; Confluence's `acli` is obscure. Default to gh-flavored grammar by analogy (`list/view/edit/create`) since that is the grammar the rest of devhub speaks. | `wiki` |
| **CI** | `gh run`, `act` | gh again. | (not yet a devhub facade) |

**Conclusion for this lane:** `gh`'s grammar is the lingua franca of developer
CLIs — three separate hosting platforms clone it, and the platform devhub most
needs to support (Bitbucket) has no competing grammar of its own. Imitating
`gh` is not a GitHub preference; it is the choice that maximizes how much an
LLM already knows on day one. Devhub's existing facades (`tasks`, `storage`)
already made this call correctly. The `git` facade is the one that never got
built.

---

## 2. How to forward to devhub

Three mechanisms, ranked by how much caller change they demand:

| # | Mechanism | Caller change | Verdict |
|---|---|---|---|
| **A** | **`PATH` shim** — a `bin/gh` that shadows the real `gh` | **None.** Every existing agent instruction, skill, script, and habit keeps working and silently routes through devhub. | **Chosen.** It is the only mechanism that fixes the stated problem, because the stated problem is that callers type `gh` and will keep typing `gh`. |
| B | Explicit `devhub gh …` | Every call site and rules file must be rewritten, and stays rewritten only until the next agent reads the old habit. | Keep as the non-shimmed entrypoint; insufficient alone. |
| C | MCP tool (`simple-mcp`) | Only helps LLM sessions that route through MCP; shell-invoked `gh` still escapes. | Complementary, later. |

### 2.1 Two traps that make the naive shim wrong

Both were measured on 2026-09-06 before any code was written.

**Trap 1 — infinite recursion.** `adapter_github.spl:32` invokes
`process_run("gh", args)`: a bare name, resolved through `PATH`. If `bin/gh`
is ahead of the real `gh` on `PATH`, then `bin/gh` → `devhub` → `gh_run` →
`bin/gh` → … forever, forking a 12-second process each cycle. This is a
fork-bomb, not a bug.

*Fix:* the shim exports `DEVHUB_REAL_GH=<absolute path to the real gh>`, and
`gh_run` prefers that variable over the bare name. The variable is set exactly
once, by the only component that can still see an unshadowed `PATH`.

**Trap 2 — startup cost.** `bin/devhub --version` takes **12.0 s** wall
(measured; the stdlib is read as source on every process start, see
`.claude/rules/commands.md`). Routing every `gh` invocation through Simple
would add 12 s to each of them. That is not a wrapper, it is a tax, and it
would be routed around within a day.

*Fix:* the shim resolves the backend **in POSIX sh** — three cheap steps, no
Simple process — and for `backend=github` it removes its own directory from
`PATH` and `exec`s the real `gh` directly. GitHub users pay ~2 ms and get
byte-identical behavior. Only a genuinely non-GitHub backend pays for the
Simple interpreter, and only because there is real translation work to do.
This also satisfies `.claude/rules/code-style.md` ("production wrappers should
execute cached compiled artifacts, not raw source") on the hot path, by not
entering the interpreter on the hot path at all.

### 2.2 Resolution order inside the shim (all in sh)

1. `$DEVHUB_GIT_BACKEND` — explicit override, wins outright.
2. `git_backend:` under the `devhub:` section of `.spipe/config.sdn` — the
   repo's committed answer.
3. Host sniff of `git remote get-url origin`: `github.com` → `github`,
   `bitbucket.org` → `bitbucket`, anything else → `github` (safe default:
   behaves exactly as today).

---

## 3. Transforming LLM input → backend, and backend output → famous shape

The wrapper is a **bidirectional translator**, and the two directions have
different failure modes.

### 3.1 Inbound: gh argv → Bitbucket argv

The LLM writes gh flags. Bitbucket's command layer wants its own. The mapping
is small and total for the covered verbs:

| gh | devhub bb | Note |
|---|---|---|
| `pr create --title T` | `pr create --title T` | identical |
| `pr create --head B` | `pr create --source B` | rename |
| `pr create --base B` | `pr create --dest B` | rename |
| `pr create --body B` | `pr create --body B` | **required adding `description` to the Bitbucket create payload** — `bb_build_create_pr_body` had no body field at all, so a PR body was silently dropped |
| `pr create --reviewer U` | `pr create --reviewer U` | identical (Bitbucket wants a UUID, not a username) |
| `pr list --state closed` | `pr list --state DECLINED` | gh has 4 states, Bitbucket 4 differently-named ones |
| `pr view N` | `pr view N` | identical |
| `pr merge N` | `merge N` | Bitbucket's merge is top-level, not under `pr` |
| `pr review N --approve` | `approve N` | same |
| `pr comment N --body B` | `comment post N --content B` | rename + renest |
| `repo view` | `repo view` | identical |

**Rule for anything not in the table:** fail loudly with a named error
(`gh pr <verb> is not supported on the bitbucket backend`), exit 1. Never
silently drop a flag and never approximate — a PR opened against the wrong
base branch because `--base` was ignored is worse than no PR.

### 3.2 Outbound: Bitbucket JSON → gh JSON

An LLM that asks for `--json number,title,state,url` expects gh's field names.
Bitbucket's REST 2.0 answers with different ones. The normalizer is a pure
function over parsed JSON:

| gh field | Bitbucket path |
|---|---|
| `number` | `id` |
| `title` | `title` |
| `state` | `state`, with `DECLINED` → `CLOSED`, `MERGED` → `MERGED`, `OPEN` → `OPEN` |
| `url` | `links.html.href` |
| `headRefName` | `source.branch.name` |
| `baseRefName` | `destination.branch.name` |
| `author.login` | `author.nickname` |
| `body` | `description` |
| `createdAt` / `updatedAt` | `created_on` / `updated_on` |
| `isDraft` | *(absent — Bitbucket has no draft PRs)* emitted as `false` |

Being explicit about the last row matters: the honest answer to "does this
backend have drafts" is *no*, and emitting `false` rather than omitting the key
keeps the shape stable for a consumer that indexes it.

---

## 4. Configuration: what goes where

### 4.1 Precedence (single chain, one resolver)

```
--backend flag  >  DEVHUB_* env  >  .spipe/config.sdn [devhub]  >  ~/.config/itf/config.sdn  >  git remote sniff  >  honest error
```

Rationale per rung: the flag is the caller's explicit intent; env is the
session/CI override; `.spipe/config.sdn` is committed and shared by the whole
team, so it is the right home for "this repo lives on Bitbucket"; the
`~/.config/itf` files stay authoritative for per-user settings and remain
backward compatible; the git-remote sniff means a fresh clone works with zero
configuration. Reaching the end without an answer is an **error naming what to
set**, never a silent default.

### 4.2 Secrets: by reference, never by value

`.spipe/config.sdn` is a **git-tracked file** (verified: `git ls-files` lists
it, `git check-ignore` does not). Therefore:

- **Tracked config carries:** which backend, the API endpoint/host, the
  workspace and repo slug, defaults. Non-secret routing facts.
- **Tracked config never carries a literal credential.** It carries a
  *reference*: `token_env: BB_TOKEN` names an environment variable, and the
  existing `token_cmds` mechanism (already in `config.spl`) names a shell
  command that prints a secret — the standard pattern for a password manager
  or `gh auth token`.
- Literal tokens continue to live in `~/.config/itf/auth.sdn`, mode-0600
  territory, outside the repo.

This is an assumption the goal did not state explicitly ("config … should
specify what real backend and login/access information"): access information
is recorded **as a resolvable reference**, and the resolution happens at call
time. Storing a Bitbucket token in a tracked file would leak it to every clone
and every CI log, so the reference form is the only production-acceptable
reading.

### 4.3 Shape

```sdn
devhub:
  git_backend: bitbucket        # github | bitbucket
  bb_workspace: acme            # Bitbucket workspace slug
  bb_repo: widgets              # Bitbucket repository slug
  bb_token_env: BB_TOKEN        # NAME of the env var holding the token
```

---

## 5. Deliberately not built (recorded, not silently skipped)

- **`bin/mc` and `bin/jira` shims.** The same shim + resolver pattern applies
  verbatim to the storage and tasks facades, which are already mc- and
  gh-shaped. Not built in this lane: `gh` is where the demonstrated bypass is,
  and one proven shim is worth more than three speculative ones. Filed as a
  todo rather than scaffolded.
- **GitLab (`glab`) backend.** The resolver and normalizer are written so a
  third backend is a table entry, but no GitLab adapter exists to route to.
- **`gh pr create --template`, `--fill`, `--web`, and interactive prompts.**
  Interactive flows have no meaning under an LLM caller; `--web` needs a
  browser. These fall through to the honest unsupported error on non-GitHub
  backends and work normally on GitHub (where the shim execs real `gh`).
