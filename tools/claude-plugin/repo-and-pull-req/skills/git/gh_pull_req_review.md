# GitHub Pull Request Review Skill

Search aliases: `self approve`, `approve PR`, `author cannot approve`.

Canonical same-author help: `spipe self-review-guide`. Searches for `self
approve`, `approve PR`, or `author cannot approve` route there. On preflight
same-author detection or a rejected author `APPROVE`, print its exact-head
review, one protected dispatch command, and exact-head poll/remediation steps;
never retry provider approval.

Autonomous PR review. Checks PR status, processes review comments,
fixes code or replies, then branches by `--level`:

- **L1** (default): post review, opportunistic auto-rebase + merge if
  PR is **already** APPROVED at check time. Single-pass, no polling.
  This is the existing behavior — preserved verbatim.
- **L2**: post review and run the Codex-first reviewer. An independent
  credential may submit a provider approval; the author credential instead
  dispatches the scoped `SPipe Self Review Admission` after a high-effort exact
  review reports zero P0/P1. Poll required checks and merge via
  `gh pr merge --squash`.
- **L3**: post review, wait for an eligible independent provider `User`
  account (not a GitHub App) to submit `APPROVED`, poll checks, and merge. This
  provider type is not proof that a person operated the account.

`--level` is read from env `CLI_LEVEL` (set by the dispatcher) or
defaults to `1`. Older state files with no `level` key default to `1`.

## Prerequisites

- `gh` CLI authenticated
- Active PR (need PR number and branch name)

## Procedure

### Step 1 — Check PR Status

```bash
REPO=$(gh repo view --json nameWithOwner --jq .nameWithOwner)
PR_STATUS=$(gh pr view "${PR_NUMBER}" --json state,reviewDecision,reviews,url,headRefName)
STATE=$(echo "$PR_STATUS" | jq -r .state)
REVIEW_DECISION=$(echo "$PR_STATUS" | jq -r .reviewDecision)
BRANCH=$(echo "$PR_STATUS" | jq -r .headRefName)
HEAD_SHA=$(gh pr view "${PR_NUMBER}" --repo "${REPO}" --json headRefOid --jq .headRefOid)
```

- If `STATE == "MERGED"` or `STATE == "CLOSED"`: exit, run post-merge cleanup
- If there are no pending reviews or unresolved comments, skip only Steps 2-4.
  Continue to Step 5: a clean L2/L3 PR still requires the Codex-first verdict,
  scoped self-review dispatch or provider approval, required-check polling, and
  merge-state handling. A clean L1 PR must likewise reach its opportunistic
  merge decision.

For same-author L2 admission, review exactly `HEAD_SHA`. The Simple hosted
workflow is valid only when `REPO == ormastes/simple`; its dispatch must include
`-f expected_head_sha="$HEAD_SHA"`. For every other repository, use the generic
SPipe evaluate-then-approve path or fail closed—never dispatch a same-number
Simple PR.

### Step 2 — Fetch Review Comments

```bash
# Get all review comments
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

#### L2 — Provider approval or scoped self-review admission + poll-merge

1. Invoke `agents/review_loop_codex_first.md` to get
   `verdict ∈ {approve, request-changes, comment}` plus `approver` and
   `verdict_source`. Also require the exact reviewed `head_sha`, model,
   effort, and P0/P1 counts. Persist them in state JSON.
2. If `verdict == approve`:
   ```bash
   REPO=$(gh repo view --json nameWithOwner --jq .nameWithOwner)
   PR_JSON=$(gh api "repos/${REPO}/pulls/${PR_NUMBER}")
   HEAD_SHA=$(printf '%s\n' "$PR_JSON" | jq -er .head.sha)
   BASE_SHA=$(printf '%s\n' "$PR_JSON" | jq -er .base.sha)
   AUTHOR_ID=$(printf '%s\n' "$PR_JSON" | jq -er .user.id)
   ACTOR_ID=$(gh api user --jq .id)
   ```

   If `ACTOR_ID != AUTHOR_ID`, submit a provider approval. GitHub remains the
   authority for reviewer eligibility. Any rejected submission is terminal for
   this loop; save `status=blocked-provider-approval`, post one comment, cancel
   the schedule, and exit rather than retrying.

   If `ACTOR_ID == AUTHOR_ID`, never call `gh pr review --approve`. Require the
   reviewer result to bind `HEAD_SHA`, use effort `high|xhigh|max|ultra`, and
   report `p0_count=0` and `p1_count=0`. Require non-empty `SESSION_ID` and
   `REVIEWER_MODEL`. Only when `REPO == ormastes/simple`, dispatch that
   repository's trusted default-branch workflow once for the exact
   `HEAD_SHA:BASE_SHA` scope:

   ```bash
   gh workflow run review-admission.yml --repo "$REPO" --ref main \
     -f pull_request_number="$PR_NUMBER" \
     -f expected_head_sha="$HEAD_SHA" \
     -f session_id="$SESSION_ID" \
     -f reviewer_model="$REVIEWER_MODEL" \
     -f reviewer_effort="$REVIEWER_EFFORT" \
     -f self_attestation='PASS:0:0'
   ```

   For every other `REPO`, do not run this hosted workflow: invoke
   `spipe_self_review_privilege_evaluate` for the closed exact-head request and
   invoke `spipe_self_review_approve` only on allow. If that protected generic
   route is unavailable or denies, fail closed.

   Persist `admission_dispatched=true`, `admission_scope=HEAD_SHA:BASE_SHA`, and
   `status=awaiting-self-review-admission`. While that scope is pending, poll;
   do not redispatch every cycle. Missing admission prerequisites or a failed
   dispatch are terminal `blocked-self-review-admission`: save state, post one
   comment, cancel the schedule, and exit.
3. Poll the exact-head admission and all provider-required checks. Accept only
   the latest `SPipe Self Review Admission` check on `HEAD_SHA` from GitHub
   Actions App ID `15368`. `success` sets `self_review_admitted=true`.
   `failure`, `action_required`, `cancelled`, `timed_out`, or `skipped` is a
   terminal `blocked-self-review-admission`; cancel and require an explicit
   restart with a fresh exact-state review. A changed head/base resets the old
   scope and also requires a fresh review before dispatch. Pushes, PR/base
   edits, protected-base pushes, policy/ruleset changes, and the ten-minute
   expiry invalidate the old admission.
4. If `(bot_approved || self_review_admitted) && checks_passing &&
   !merge_attempted`:
   ```bash
   gh pr merge "${PR_NUMBER}" --squash --delete-branch
   MERGE_RC=$?
   ```
   On 403/409/401: blocked, see *Failure Modes*. On success:
   `status=merged`.

#### L3 — Poll for an eligible independent provider user-account approval

1. Post review comments only. Do NOT bot-approve.
2. Reset `USER_ACCOUNT_APPROVED=false` at the start of every cycle; never seed
   it from persisted `user_account_approved` or legacy `human_approved`. Poll
   for a current exact-head independent `APPROVED` review whose provider actor
   type is `User`, not `Bot`/App. This proves only the provider account class
   and independence from the author; it does not prove a human operated it:
   ```bash
   PR_JSON=$(gh api "repos/${REPO}/pulls/${PR_NUMBER}")
   HEAD_SHA=$(printf '%s\n' "$PR_JSON" | jq -er .head.sha)
   AUTHOR_ID=$(printf '%s\n' "$PR_JSON" | jq -er '.user.id | tostring')
   REVIEWS_JSON=$(gh api --paginate \
     "repos/${REPO}/pulls/${PR_NUMBER}/reviews?per_page=100" | jq -s 'add')
   USER_ACCOUNT_APPROVED_COUNT=$(printf '%s\n' "$REVIEWS_JSON" |
     jq --arg head "$HEAD_SHA" --arg author "$AUTHOR_ID" '
       [.[] | select(.commit_id == $head)]
       | sort_by(.submitted_at, .id)
       | group_by(.user.id)
       | map(last)
       | [.[] | select(.state == "APPROVED"
                       and (.user.id | tostring) != $author
                       and .user.type == "User")]
       | length')
   if [ "$USER_ACCOUNT_APPROVED_COUNT" -gt 0 ]; then
     USER_ACCOUNT_APPROVED=true
   else
     USER_ACCOUNT_APPROVED=false
   fi
   ```
3. Poll checks (same query as L2).
4. If `user_account_approved && checks_passing && !merge_attempted`:
   ```bash
   gh pr merge "${PR_NUMBER}" --squash --delete-branch
   ```
   Failure handling identical to L2.

### Step 5b — Failure-Mode Capture (L2/L3 only)

For each provider-approval, admission-dispatch, and merge call, classify the
exit. Every nonzero admission dispatch and rejected same-author provider
approval is terminal; unknown nonzero exits are not safe to retry automatically.

| Exit / HTTP | State field        | Action                                  |
|-------------|--------------------|-----------------------------------------|
| 0 (success) | proceed            | Continue                                |
| 403         | `blocked`          | Post one comment ("Bot lacks permission"), cancel schedule, exit |
| 409         | `blocked-conflict` | Post one comment ("Merge conflict — manual rebase needed"), cancel schedule, exit |
| 401         | `blocked-auth`     | Post one comment ("Bot token invalid — re-run setup"), cancel schedule, exit |
| other ≠ 0   | `blocked`          | Preserve error, post once, cancel schedule, exit |

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
