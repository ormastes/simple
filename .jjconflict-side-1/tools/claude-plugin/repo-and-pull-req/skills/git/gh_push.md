# GitHub Push Skill

Push code to GitHub as a Pull Request using jj bookmark pattern.

## IMPORTANT: PR Branch Strategy

This project works on main (no persistent branches). For PRs, we create a
TEMPORARY jj bookmark that maps to a git branch, push it, create the PR,
then clean up after merge.

## Prerequisites

- `gh` CLI authenticated (`gh auth status`; if not → run gh_setup)
- Local changes committed via `jj commit`
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

# Post-rebase file count check
FILE_COUNT_AFTER=$(git ls-files | wc -l | tr -d ' ')
echo "File count after rebase: ${FILE_COUNT_AFTER}"
# ABORT if unexpected reduction (> 5% loss)
```

### Step 3 — Create Temporary PR Bookmark

Derive branch name from the commit message (kebab-case slug):

```bash
# Get commit description for slug
COMMIT_MSG=$(jj log -r @- --no-graph -T 'description')
SLUG=$(echo "$COMMIT_MSG" | head -1 | tr '[:upper:]' '[:lower:]' | sed 's/[^a-z0-9]/-/g' | sed 's/--*/-/g' | head -c 50)
BRANCH="pr/${SLUG}"

# Create bookmark on the committed change
jj bookmark create "${BRANCH}" -r @-

# Push the bookmark (creates the remote branch)
jj git push --bookmark "${BRANCH}"
```

### Step 4 — Create Pull Request

```bash
# Generate PR title from commit first line
PR_TITLE=$(jj log -r @- --no-graph -T 'description' | head -1)

# Generate PR body from diff stats + commit message
PR_BODY=$(cat <<'BODY_EOF'
## Summary
$(jj log -r @- --no-graph -T 'description')

## Changes
$(jj diff --stat -r @-)

## Checklist
- [ ] Tests pass
- [ ] No new warnings
BODY_EOF
)

# Create the PR
gh pr create --base main --head "${BRANCH}" \
  --title "${PR_TITLE}" \
  --body "${PR_BODY}"
```

Record the PR URL and number for subsequent skills (wiki, review).

### Step 5 — Report

Print:
- PR URL
- Branch name: `${BRANCH}`
- Changed files count
- Suggest: run `/repo_and_pull_req wiki` to create knowledge pages
- Suggest: run `/repo_and_pull_req review loop <pr#>` for autonomous review

## Post-Merge Cleanup

After the PR is merged (called manually or by review_loop agent):

```bash
jj git fetch
jj rebase -d main@origin

# Delete the temporary bookmark
jj bookmark delete "${BRANCH}"
jj git push --bookmark "${BRANCH}" --deleted
```

## Integration

- **With /sync**: Reuses file-count guards from /sync skill
- **With jira_push**: If Jira configured (`jira me` succeeds), also run jira_push to cross-link
- **With .sstack state**: If `.sstack/<feature>/state.md` exists, include acceptance criteria in PR body
