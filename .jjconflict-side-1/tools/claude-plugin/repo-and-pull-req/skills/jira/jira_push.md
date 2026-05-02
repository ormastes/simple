# Jira Push Skill

Create or update Jira issues to track work being pushed as a PR.

## Prerequisites

- Our jira-cli configured (`bin/jira auth status` succeeds; if not → run jira_setup)
- PR already created (from gh_push) — need PR URL and number

## Procedure

### Step 1 — Determine Issue Context

1. Check if PR description already contains a Jira key (e.g., `PROJ-123`)
2. Check if branch name contains a Jira key
3. If linked issue found: go to Step 3 (update)
4. If no issue: go to Step 2 (create)

### Step 2 — Create New Issue

Extract info from git context:

```bash
# Get commit message
COMMIT_MSG=$(jj log -r @- --no-graph -T 'description')
SUMMARY=$(echo "$COMMIT_MSG" | head -1)
BODY=$(echo "$COMMIT_MSG" | tail -n +2)

# Detect type from commit prefix
# feat → Story, fix → Bug, refactor/chore/docs/test/perf → Task
TYPE="Task"
case "$SUMMARY" in
  feat*) TYPE="Story" ;;
  fix*)  TYPE="Bug" ;;
esac

# Create issue
bin/jira issue create \
  --type "${TYPE}" \
  --summary "${SUMMARY}" \
  --body "${BODY}\n\nPR: ${PR_URL}" \
  --priority Medium
```

Record the issue key (e.g., `SIMPLE-42`).

### Step 3 — Update Existing Issue

```bash
# Add comment with push details
DIFF_STAT=$(jj diff --stat -r @-)
bin/jira issue comment "${ISSUE_KEY}" \
  --body "Code pushed. PR: ${PR_URL}\n\nChanges:\n${DIFF_STAT}"

# Transition to "In Review"
bin/jira issue move "${ISSUE_KEY}" "In Review" 2>/dev/null || true
```

### Step 4 — Cross-Link PR and Issue

```bash
# Add Jira key to PR description (if not already present)
EXISTING_BODY=$(gh pr view "${PR_NUMBER}" --json body --jq .body)
if ! echo "$EXISTING_BODY" | grep -q "${ISSUE_KEY}"; then
  gh pr edit "${PR_NUMBER}" --body "${EXISTING_BODY}\n\nJira: ${ISSUE_KEY}"
fi
```

## Issue Type Mapping

| Commit Prefix | Jira Type |
|---------------|-----------|
| feat          | Story     |
| fix           | Bug       |
| refactor      | Task      |
| perf          | Task      |
| docs          | Task      |
| test          | Sub-task  |
| chore         | Task      |

## Status Transitions

| Event           | Jira Transition |
|-----------------|-----------------|
| PR created      | → In Review     |
| PR approved     | → Approved      |
| PR merged       | → Done          |
| PR closed       | → Won't Do      |
