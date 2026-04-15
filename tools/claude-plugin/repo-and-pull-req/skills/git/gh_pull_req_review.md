# GitHub Pull Request Review Skill

Single-pass autonomous PR review. Checks PR status, processes review comments,
fixes code or replies, auto-rebases when all resolved.

## Prerequisites

- `gh` CLI authenticated
- Active PR (need PR number and branch name)

## Procedure

### Step 1 — Check PR Status

```bash
PR_STATUS=$(gh pr view "${PR_NUMBER}" --json state,reviewDecision,reviews,url,headRefName)
STATE=$(echo "$PR_STATUS" | jq -r .state)
REVIEW_DECISION=$(echo "$PR_STATUS" | jq -r .reviewDecision)
BRANCH=$(echo "$PR_STATUS" | jq -r .headRefName)
```

- If `STATE == "MERGED"` or `STATE == "CLOSED"`: exit, run post-merge cleanup
- If no pending reviews and no unresolved comments: exit (nothing to do)

### Step 2 — Fetch Review Comments

```bash
# Get all review comments
REPO=$(gh repo view --json nameWithOwner --jq .nameWithOwner)
COMMENTS=$(gh api "repos/${REPO}/pulls/${PR_NUMBER}/comments" \
  --jq '.[] | {id, path, line, body, user: .user.login, created_at, in_reply_to_id}')

# Get PR-level comments
PR_COMMENTS=$(gh api "repos/${REPO}/issues/${PR_NUMBER}/comments" \
  --jq '.[] | {id, body, user: .user.login, created_at}')

# Get review summaries
REVIEWS=$(gh api "repos/${REPO}/pulls/${PR_NUMBER}/reviews" \
  --jq '.[] | {id, state, body, user: .user.login}')
```

### Step 3 — Process Each Unresolved Comment

For each comment that has no reply from us:

**Classify the comment:**

| Category   | Indicators | Action |
|------------|-----------|--------|
| CODE_FIX   | "change", "fix", "bug", "should be", suggestion block | Edit code |
| QUESTION   | "why", "what", "how", "?", "explain" | Reply with explanation |
| NIT        | "nit", "style", "minor", "optional" | Apply if reasonable |
| APPROVAL   | "LGTM", "looks good", "+1", approval review | No action |

**For CODE_FIX:**

1. Read the file at the specified path and line:
   ```bash
   # comment.path and comment.line tell us where
   ```
2. Understand the requested change from the comment body
3. Apply the fix using Edit tool
4. Commit: `jj commit -m "fix: address review — <summary of change>"`
5. Reply to comment:
   ```bash
   gh api "repos/${REPO}/pulls/${PR_NUMBER}/comments/${COMMENT_ID}/replies" \
     -f body="Fixed. Applied the suggested change."
   ```

**For QUESTION:**

1. Read surrounding code context
2. Generate a clear, concise explanation
3. Reply:
   ```bash
   gh api "repos/${REPO}/pulls/${PR_NUMBER}/comments/${COMMENT_ID}/replies" \
     -f body="<explanation>"
   ```

**For NIT:**

1. If reasonable: apply the style fix, commit, reply "Applied"
2. If debatable: reply explaining the current choice

### Step 4 — Push Fixes

If any code changes were made:

```bash
# File count safety guard
FILE_COUNT=$(git ls-files | wc -l | tr -d ' ')
echo "File count: ${FILE_COUNT}"

# Push
jj git push --bookmark "${BRANCH}"
```

### Step 5 — Check Resolution and Auto-Rebase

```bash
# Re-check status after processing
UPDATED_STATUS=$(gh pr view "${PR_NUMBER}" --json reviewDecision,reviews)
DECISION=$(echo "$UPDATED_STATUS" | jq -r .reviewDecision)
```

If `DECISION == "APPROVED"` and all comments addressed:

```bash
# Rebase onto latest main
jj git fetch
jj rebase -d main@origin

# File count guard
FILE_COUNT_AFTER=$(git ls-files | wc -l | tr -d ' ')

# Push rebased branch
jj git push --bookmark "${BRANCH}"

# Optionally auto-merge (ask user first in single-pass mode)
# gh pr merge "${PR_NUMBER}" --rebase --delete-branch
```

### Step 6 — Report

Print summary:
- Comments processed: N
- Fixes applied: N
- Questions answered: N
- PR status: approved/changes_requested/pending
- Next action: "Run `/repo_and_pull_req review loop <pr#>` for continuous monitoring"

## Post-Merge Cleanup

```bash
jj git fetch
jj rebase -d main@origin
jj bookmark delete "${BRANCH}"
jj git push --bookmark "${BRANCH}" --deleted
```
