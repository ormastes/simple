---
name: repo_and_pull_req
description: GitHub and Jira/Confluence integration — setup, push, wiki, and autonomous PR review. Routes to sub-skills in git/ and jira/ directories.
---

# Repo & Pull Request Skill — Dispatcher

Unified skill for GitHub, Bitbucket, and Jira/Confluence operations:
setup, push, wiki, and PR review (with 3-level review state machine).

## Usage

```
/repo_and_pull_req <command> [args] [--target=gh|bb|jira] [--level=1|2|3]
```

## Commands

| Command | Example | Description |
|---------|---------|-------------|
| `setup gh` | `/repo_and_pull_req setup gh` | Install and configure gh CLI |
| `setup bb` | `/repo_and_pull_req setup bb` | Install + configure Bitbucket Repo Access Token (Agent C) |
| `setup jira` | `/repo_and_pull_req setup jira` | Install and configure jira-cli + Atlassian account |
| `push` | `/repo_and_pull_req push --target=gh --level=1` | Push code as PR + (optionally) create issue |
| `wiki gh` | `/repo_and_pull_req wiki gh` | Create/update GitHub wiki page |
| `wiki jira` | `/repo_and_pull_req wiki jira` | Create/update Confluence page |
| `wiki` | `/repo_and_pull_req wiki` | Update both wikis |
| `review <pr#>` | `/repo_and_pull_req review 42 --target=gh --level=1` | Single-pass PR review (L1, current behavior) |
| `review <pr#> --level=2` | `/repo_and_pull_req review 42 --level=2` | Bot-approves + auto-merges (poll 60s, 24h cap) |
| `review <pr#> --level=3` | `/repo_and_pull_req review 42 --level=3` | Wait for human approval + merge (poll 5m, 7d cap) |
| `review loop <pr#>` | `/repo_and_pull_req review loop 42 --level=2` | Start scheduled review loop at the level's cadence |
| `review stop <pr#>` | `/repo_and_pull_req review stop 42` | Stop review loop (cancels schedule for any level) |

### Flags

| Flag        | Default                                                                                                | Notes |
|-------------|--------------------------------------------------------------------------------------------------------|-------|
| `--target=` | detect from `git remote get-url origin` (`github.com`→`gh`, `bitbucket.org`→`bb`); **error** if neither matches | Routes to git/, bb/, or jira/ sub-skill tree |
| `--level=`  | `1`                                                                                                    | 1=one-shot/opportunistic-merge (current), 2=bot-approve+auto-merge, 3=wait-human+merge |

`--target=jira` is **NOT valid with `--level=2|3`** — Jira tracks
tickets, not code review. Reject the combination with a clear error:

```
ERROR: --target=jira only supports --level=1. Use --target=gh or
       --target=bb for L2/L3 bot/human approval and auto-merge.
```

Older state files (no `level`/`target` keys) default to `level=1` and
the detected target — fully backward compatible.

## Dispatch Logic

Argument: `$ARGUMENTS`

### Parse (positional + flags)

```bash
COMMAND=""
SUBCOMMAND=""    # gh|jira|loop|stop|<pr#>
EXTRA=""         # remaining positional
TARGET=""        # --target=
LEVEL=""         # --level=

for arg in $ARGUMENTS; do
  case "$arg" in
    --target=*) TARGET="${arg#--target=}" ;;
    --level=*)  LEVEL="${arg#--level=}"  ;;
    *)
      if [ -z "$COMMAND" ]; then
        COMMAND="$arg"
      elif [ -z "$SUBCOMMAND" ]; then
        SUBCOMMAND="$arg"
      else
        EXTRA="$EXTRA $arg"
      fi
      ;;
  esac
done

# Defaults
if [ -z "$TARGET" ]; then
  TARGET=$(git remote get-url origin 2>/dev/null | awk '
    /github\.com/    {print "gh";   exit}
    /bitbucket\.org/ {print "bb";   exit}')
  if [ -z "$TARGET" ]; then
    echo "ERROR: cannot detect --target from origin URL; pass --target=gh|bb|jira" >&2
    exit 2
  fi
fi
LEVEL="${LEVEL:-1}"

# Validate target+level combo
if [ "$TARGET" = "jira" ] && [ "$LEVEL" != "1" ]; then
  echo "ERROR: --target=jira only supports --level=1. Use --target=gh|bb for L2/L3." >&2
  exit 2
fi
```

### Route

**`setup gh`:**
Read `tools/claude-plugin/repo-and-pull-req/skills/git/gh_setup.md` and follow procedure.

**`setup bb`:**
Read `tools/claude-plugin/repo-and-pull-req/skills/bb/bb_setup.md` and follow procedure (owned by Agent C).

**`setup jira`:**
Read `tools/claude-plugin/repo-and-pull-req/skills/jira/jira_setup.md` and follow procedure.

**`push`:**
1. Pre-check auth for the chosen target:
   - `gh`: `gh auth status` — if fails, redirect to `setup gh`
   - `bb`: `itf bb status` (or equivalent) — if fails, redirect to `setup bb`
2. Read and follow:
   - `gh`: `tools/claude-plugin/repo-and-pull-req/skills/git/gh_push.md`
   - `bb`: `tools/claude-plugin/repo-and-pull-req/skills/bb/bb_push.md`
3. Pass `--level=$LEVEL` through to the post-create review trigger.
4. If Jira configured (`bin/jira auth status` succeeds):
   Also read and follow `tools/claude-plugin/repo-and-pull-req/skills/jira/jira_push.md`
   (issue linkage only — does not gate review).

**`wiki gh`:**
Read `tools/claude-plugin/repo-and-pull-req/skills/git/gh_wiki.md` and follow procedure.

**`wiki jira`:**
Read `tools/claude-plugin/repo-and-pull-req/skills/jira/jira_wiki.md` and follow procedure.

**`wiki`** (no platform specified):
Run `wiki gh`. If Jira configured, also run `wiki jira`.

**`review <pr#>`:**
1. Set env: `PR_NUMBER=$SUBCOMMAND`, `CLI_LEVEL=$LEVEL`, `CLI_TARGET=$TARGET`.
2. Route by target:
   - `gh`: read and follow `tools/claude-plugin/repo-and-pull-req/skills/git/gh_pull_req_review.md` (which itself branches on `$CLI_LEVEL`).
   - `bb`: read and follow `tools/claude-plugin/repo-and-pull-req/skills/bb/bb_pull_req_review.md` (Agent C).
   - `jira`: read and follow `tools/claude-plugin/repo-and-pull-req/skills/jira/jira_pull_req_review.md` (L1 only — already validated above).
3. If Jira is also linked AND target ≠ jira: additionally follow
   `skills/jira/jira_pull_req_review.md` for ticket comment exchange
   (does not affect L2/L3 merge gate).

**`review loop <pr#>`:**
Start the scheduled review at the level's cadence:

```bash
case "$LEVEL" in
  1) /schedule 1h  /repo_and_pull_req review $PR --level=1 --target=$TARGET ;;
  2) /schedule 60s /repo_and_pull_req review $PR --level=2 --target=$TARGET ;;
  3) /schedule 5m  /repo_and_pull_req review $PR --level=3 --target=$TARGET ;;
esac
```

**`review stop <pr#>`:**
Cancel the scheduled review for this PR number (any level). This is
the canonical hook the `review_loop.md` agent calls when it sets
`status=blocked*` or hits `max-cycles`.

## Prerequisite Checks

Before any non-setup command:
- `--target=gh`: `gh auth status` — redirect to `setup gh` if fails
- `--target=bb`: `itf bb status` — redirect to `setup bb` if fails
- `--target=jira`: `bin/jira auth status` — redirect to `setup jira` if fails
- For push: verify committed changes exist (`jj st`)

## Integration

| Skill | When Used |
|-------|-----------|
| `/sync` | File count guards during push and rebase |
| `/release` | Suggested after merge for version bump |
| `/sstack` | Ship phase passes `--target` and `--review-level` through to `push`; state file used for richer PR descriptions |
