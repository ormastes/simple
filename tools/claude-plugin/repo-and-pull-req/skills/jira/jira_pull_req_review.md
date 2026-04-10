# Jira Pull Request Review Skill

Review for Jira-linked PRs. Extends gh_pull_req_review with Jira comment
handling and status transitions.

## Prerequisites

- jira-cli configured (`jira me` succeeds)
- PR linked to a Jira issue (issue key in PR description)
- `gh` CLI authenticated

## Procedure

### Step 1 — Resolve Jira Issue Key

```bash
# Extract Jira key from PR description
PR_BODY=$(gh pr view "${PR_NUMBER}" --json body --jq .body)
ISSUE_KEY=$(echo "$PR_BODY" | grep -oE '[A-Z]+-[0-9]+' | head -1)

if [ -z "$ISSUE_KEY" ]; then
  echo "No Jira issue linked to PR #${PR_NUMBER}. Skipping Jira review."
  exit 0
fi
```

### Step 2 — Check Jira Issue Comments

```bash
# View issue with comments
jira issue view "${ISSUE_KEY}" --comments 2>/dev/null

# Get recent comments via API for structured processing
JIRA_CONFIG="$HOME/.config/.jira/.config.yml"
SERVER=$(grep 'server:' "$JIRA_CONFIG" | awk '{print $2}' | sed 's|/$||')
EMAIL=$(grep 'login:' "$JIRA_CONFIG" | awk '{print $2}')

JIRA_COMMENTS=$(curl -s -u "${EMAIL}:${TOKEN}" \
  "${SERVER}/rest/api/3/issue/${ISSUE_KEY}/comment" \
  -H "Accept: application/json")
```

### Step 3 — Process Jira Comments

For new comments (since last check):

1. Read comment body
2. If contains code review feedback: classify same as gh_pull_req_review
   (CODE_FIX / QUESTION / NIT / APPROVAL)
3. Process: fix code or generate reply
4. Respond via jira-cli:
   ```bash
   jira issue comment add "${ISSUE_KEY}" --body "<reply>"
   ```

### Step 4 — Run GitHub PR Review

Delegate to gh_pull_req_review for the linked PR:
- Read and follow `skills/git/gh_pull_req_review.md`
- This handles all GitHub-side comments, fixes, and rebasing

### Step 5 — Update Jira Status

Based on PR review outcome:

```bash
# If all comments addressed
jira issue comment add "${ISSUE_KEY}" \
  --body "Review cycle complete. All comments addressed."

# If PR approved → transition
if [ "$DECISION" = "APPROVED" ]; then
  jira issue move "${ISSUE_KEY}" "Approved" 2>/dev/null || true
fi

# If PR merged → transition to Done
if [ "$STATE" = "MERGED" ]; then
  jira issue move "${ISSUE_KEY}" "Done" 2>/dev/null || true
fi
```

### Step 6 — Report

Print summary including:
- Jira issue: `${ISSUE_KEY}`
- Jira comments processed: N
- GitHub comments processed: N (from gh_pull_req_review)
- Current Jira status
- Current PR status

## Automation

Uses same scheduling as gh_pull_req_review:

```
/schedule 1h /repo_and_pull_req review <pr-number>
```

The review_loop agent handles both GitHub and Jira in each cycle.
