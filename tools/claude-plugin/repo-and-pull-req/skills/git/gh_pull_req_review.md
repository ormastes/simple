# GitHub Pull Request Review Skill

Autonomous PR review. Checks PR status, processes review comments,
fixes code or replies, then branches by `--level`:

- **L1** (default): post review, opportunistic auto-rebase + merge if
  PR is **already** APPROVED at check time. Single-pass, no polling.
  This is the existing behavior — preserved verbatim.
- **L2**: post review, run Codex-first bot reviewer, then bot-approves via
  `gh pr review --approve` only when its authenticated GitHub identity is not
  the PR author; polls checks and merges via `gh pr merge --squash`.
- **L3**: post review, wait for **human** APPROVED review (do NOT
  bot-approve), poll checks, merge.

`--level` is read from env `CLI_LEVEL` (set by the dispatcher) or
defaults to `1`. Older state files with no `level` key default to `1`.

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

### Step 5 — Per-Level Branching

Read `LEVEL="${CLI_LEVEL:-1}"`. Re-check status after processing:

```bash
UPDATED_STATUS=$(gh pr view "${PR_NUMBER}" --json reviewDecision,reviews,statusCheckRollup)
DECISION=$(echo "$UPDATED_STATUS" | jq -r .reviewDecision)
```

#### L1 — Post review only + opportunistic merge (current behavior)

If `DECISION == "APPROVED"`, at least one approval is from a login other than
the PR author, and all comments are addressed:

```bash
if ! AUTHOR=$(gh pr view "${PR_NUMBER}" --json author --jq .author.login) || [ -z "$AUTHOR" ]; then
  echo "could not determine PR author; do not merge" >&2
  exit 2
fi
REVIEWS_JSON=$(gh pr view "${PR_NUMBER}" --json reviews)
INDEPENDENT_APPROVED=$(printf '%s\n' "$REVIEWS_JSON" | jq --arg author "$AUTHOR" \
  '[.reviews[] | select(.state=="APPROVED" and .author.login != $author)] | length')
if [ "$INDEPENDENT_APPROVED" -le 0 ]; then
  echo "no independent approval; do not merge" >&2
  exit 0
fi
# Rebase onto latest main
jj git fetch
jj rebase -d main@origin

# File count guard
FILE_COUNT_AFTER=$(git ls-files | wc -l | tr -d ' ')

# Push rebased branch
jj git push --bookmark "${BRANCH}"

# Auto-merge (single-pass)
gh pr merge "${PR_NUMBER}" --rebase --delete-branch
```

L1 deviates from the arch doc table (which lists L1 as comments-only)
to preserve the existing single-pass merge-on-APPROVED behavior. No
polling, no bot-approve, no checks-wait.

#### L2 — Bot-approve via `gh pr review --approve` + poll-merge

1. Invoke `agents/review_loop_codex_first.md` to get
   `verdict ∈ {approve, request-changes, comment}` plus `approver` and
   `verdict_source`. Persist these in state JSON.
2. If `verdict == approve`:
   ```bash
   if ! AUTHOR=$(gh pr view "${PR_NUMBER}" --json author --jq .author.login) || [ -z "$AUTHOR" ]; then
     echo "could not determine PR author; do not approve" >&2
     exit 2
   fi
   if ! ACTOR=$(gh api user --jq .login) || [ -z "$ACTOR" ]; then
     echo "could not determine authenticated reviewer; do not approve" >&2
     exit 2
   fi
   if [ "$ACTOR" = "$AUTHOR" ]; then
     echo "blocked-self-review: author credential cannot approve its own PR" >&2
     exit 2
   fi
   ```
   GitHub remains the authority for configured reviewer eligibility; a rejected
   review submission blocks the workflow and must not be retried as a bypass.

   ```bash
   gh pr review "${PR_NUMBER}" --approve --body "Bot approval (${APPROVER}/${VERDICT_SOURCE})"
   APPROVE_RC=$?
   ```
   Capture HTTP status (use `gh api --include` if needed). On
   401/403/409: see *Failure Modes* in `agents/review_loop.md` —
   set `status=blocked-*`, post one comment, **cancel schedule, exit**.
3. Poll checks:
   ```bash
   CHECKS=$(gh pr checks "${PR_NUMBER}" --json bucket --jq '[.[] | .bucket] | unique')
   # All "pass" → green; any "fail" → failing; any "pending" → still running
   ```
4. If `bot_approved && checks_passing && !merge_attempted`:
   ```bash
   gh pr merge "${PR_NUMBER}" --squash --delete-branch
   MERGE_RC=$?
   ```
   On 403/409/401: blocked, see *Failure Modes*. On success:
   `status=merged`.

#### L3 — Post review only + poll for human approval + merge

1. Post review comments only. Do NOT bot-approve.
2. Poll for an independent human APPROVED review.  A GitHub `User` is the
   documented non-bot minimum; an unknown or bot account does not qualify:
   ```bash
   if ! AUTHOR=$(gh pr view "${PR_NUMBER}" --json author --jq .author.login) || [ -z "$AUTHOR" ]; then
     echo "could not determine PR author; keep waiting" >&2
     exit 2
   fi
   REVIEWS_JSON=$(gh pr view "${PR_NUMBER}" --json reviews)
   HUMAN_APPROVED_COUNT=0
   for reviewer in $(printf '%s\n' "$REVIEWS_JSON" | jq --arg author "$AUTHOR" -r \
     '.reviews[] | select(.state=="APPROVED" and .author.login != $author) | .author.login'); do
     if reviewer_type=$(gh api "users/${reviewer}" --jq .type) && [ "$reviewer_type" = "User" ]; then
       HUMAN_APPROVED_COUNT=$((HUMAN_APPROVED_COUNT + 1))
     fi
   done
   if [ "$HUMAN_APPROVED_COUNT" -gt 0 ]; then
     HUMAN_APPROVED=true
   fi
   ```
3. Poll checks (same query as L2).
4. If `human_approved && checks_passing && !merge_attempted`:
   ```bash
   gh pr merge "${PR_NUMBER}" --squash --delete-branch
   ```
   Failure handling identical to L2.

### Step 5b — Failure-Mode Capture (L2/L3 only)

For each `gh pr review --approve` and `gh pr merge` call, classify
the exit:

| Exit / HTTP | State field        | Action                                  |
|-------------|--------------------|-----------------------------------------|
| 0 (success) | proceed            | Continue                                |
| 403         | `blocked`          | Post one comment ("Bot lacks permission"), cancel schedule, exit |
| 409         | `blocked-conflict` | Post one comment ("Merge conflict — manual rebase needed"), cancel schedule, exit |
| 401         | `blocked-auth`     | Post one comment ("Bot token invalid — re-run setup"), cancel schedule, exit |
| other ≠ 0   | continue cycle     | Log and retry next cycle                |

The bot must NEVER tight-loop on auth/policy errors. Once `blocked*`,
the schedule is cancelled and the human must restart manually.

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
