# Bitbucket Push Skill

Push a committed change to Bitbucket and open a Pull Request via the
`bin/simple itf bb` adapter (REST 2.0). Mirrors `gh_push` semantics.

## IMPORTANT: PR Branch Strategy

Always create a **temporary PR-named bookmark** off the committed change.
Never push directly to `main`. The orchestrator owns the merge.

## Prerequisites

- `bb_setup` completed (`bitbucket:` token in `~/.config/itf/auth.sdn`)
- Local changes committed via `jj commit`
- `BB_WORKSPACE` + `BB_REPO` set or `--workspace`/`--repo` ready to pass
- /sync file-count safety protocol

## Procedure

### Step 1 — Pre-flight Safety

```bash
# Record baseline file count
FILE_COUNT_BEFORE=$(git ls-files | wc -l | tr -d ' ')
echo "File count before: ${FILE_COUNT_BEFORE}"

# Verify local changes are committed
jj st
# If uncommitted changes exist, commit first:
# jj commit -m "<type>: <description>"
```

### Step 2 — Fetch and Rebase

```bash
jj git fetch
jj rebase -d main@origin

# File count guard
FILE_COUNT_AFTER=$(git ls-files | wc -l | tr -d ' ')
if [ "${FILE_COUNT_AFTER}" -lt "${FILE_COUNT_BEFORE}" ]; then
  echo "ABORT: file count dropped (${FILE_COUNT_BEFORE} -> ${FILE_COUNT_AFTER})"
  exit 1
fi
```

### Step 3 — Create Temporary PR Bookmark

Derive branch name from the commit message (kebab-case slug):

```bash
COMMIT_MSG=$(jj log -r @- --no-graph -T 'description')
SLUG=$(echo "$COMMIT_MSG" | head -1 | tr '[:upper:]' '[:lower:]' | sed 's/[^a-z0-9]/-/g' | sed 's/--*/-/g' | head -c 50)
BRANCH="pr/${SLUG}"

# Create bookmark on the committed change
jj bookmark create "${BRANCH}" -r @-

# Push the bookmark (creates the remote branch on Bitbucket)
jj git push --bookmark "${BRANCH}"
```

### Step 4 — Create Pull Request

Use `bin/simple itf bb pr create`. Title is the first line of the commit
message; description is the rest.

```bash
TITLE=$(echo "$COMMIT_MSG" | head -1)

bin/simple itf bb pr create \
  --workspace "${BB_WORKSPACE}" --repo "${BB_REPO}" \
  --title "${TITLE}" \
  --source "${BRANCH}" --dest main \
  --json
```

Optional: add explicit reviewers (UUIDs only — usernames deprecated 2019):

```bash
bin/simple itf bb pr create ... \
  --reviewer "{504c3b62-8120-4f0c-a7bc-87800b9d6f70}" \
  --reviewer "{...}"
```

Capture the PR id from JSON output:

```bash
PR_ID=$(bin/simple itf bb pr create ... --json | jq -r .id)
echo "Created PR #${PR_ID}"
```

### Step 5 — Report

Print to user:
- PR id
- PR web URL (from `pr.links.html.href`)
- Branch name pushed
- Reviewers requested

### Post-Merge Cleanup

After PR is merged via `bb_pull_req_review` or `bin/simple itf bb merge`:

```bash
# Delete local bookmark
jj bookmark delete "${BRANCH}"
# Remote source branch is auto-closed if --keep-source was NOT passed
```

## Integration

- **With /sync**: reuses file-count guards from /sync
- **With `bb_pull_req_review`**: hands off PR id for review pass
- **With .sstack state**: include acceptance criteria from
  `.sstack/<feature>/state.md` in PR body when present

## Error Handling

| Error                                  | Action                                       |
|----------------------------------------|----------------------------------------------|
| `blocked-auth: 401/403`                | Re-run `bb_setup` to mint a fresh token      |
| `not found 404`                        | Wrong workspace/repo slug                    |
| `409` on PR create                     | Source branch missing (push the branch first)|
| `429`                                  | Rate-limited; respect `Retry-After` header   |
