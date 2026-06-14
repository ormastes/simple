# Bitbucket Pull Request Review Skill

Single-pass autonomous PR review for Bitbucket Cloud. Checks PR status,
processes review comments, fixes code or replies, auto-rebases when all
resolved. Mirrors `gh_pull_req_review` against the `bin/simple itf bb`
adapter.

## Prerequisites

- `bb_setup` completed
- `BB_WORKSPACE` + `BB_REPO` exported
- `PR_ID` known (from `bb_push` or user input)

## Procedure

### Step 1 — Check PR Status

```bash
# Snapshot the PR
bin/simple itf bb pr view "${PR_ID}" --json > /tmp/bb_pr_${PR_ID}.json

STATE=$(jq -r .state /tmp/bb_pr_${PR_ID}.json)
SOURCE=$(jq -r .source.branch.name /tmp/bb_pr_${PR_ID}.json)
DEST=$(jq -r .destination.branch.name /tmp/bb_pr_${PR_ID}.json)

if [ "${STATE}" != "OPEN" ]; then
  echo "PR is ${STATE}; nothing to review."
  exit 0
fi
```

### Step 2 — Fetch Review Comments

```bash
bin/simple itf bb comment list "${PR_ID}" --json > /tmp/bb_comments_${PR_ID}.json

# Extract unresolved comments authored by reviewers (not by us)
COMMENTS=$(jq '.values[] | {id, content: .content.raw, path: .inline.path,
  line: .inline.to, user: .user.display_name, parent: .parent.id}'
  /tmp/bb_comments_${PR_ID}.json)
```

### Step 3 — Process Each Unresolved Comment

For each comment without a reply from us:

**Classify the comment:**

| Category   | Indicators                                            | Action            |
|------------|-------------------------------------------------------|-------------------|
| CODE_FIX   | "change", "fix", "bug", "should be", suggestion block | Edit code         |
| QUESTION   | "why", "what", "how", "?", "explain"                  | Reply with answer |
| NIT        | "nit", "style", "minor", "optional"                   | Apply if reasonable |
| APPROVAL   | "LGTM", "looks good", "+1"                            | No action         |

**For CODE_FIX:**

1. Read the file at `comment.inline.path` near `comment.inline.to`.
2. Apply the requested change with the Edit tool.
3. Commit: `jj commit -m "fix: address review — <summary>"`
4. Push: `jj git push --bookmark "${BRANCH}"`
5. Reply inline at the same path/line:

```bash
bin/simple itf bb comment post "${PR_ID}" \
  --content "Fixed. Applied the suggested change." \
  --inline-path "${COMMENT_PATH}" --inline-to "${COMMENT_LINE}"
```

**For QUESTION:**

```bash
bin/simple itf bb comment post "${PR_ID}" \
  --content "<your explanation>" \
  --inline-path "${COMMENT_PATH}" --inline-to "${COMMENT_LINE}"
```

**For NIT:**

If reasonable, apply the style fix and reply "Applied".
Otherwise reply with the rationale.

### Step 4 — Push Fixes

```bash
# File count safety guard
FILE_COUNT=$(git ls-files | wc -l | tr -d ' ')
echo "File count: ${FILE_COUNT}"

# Push the updated branch
jj git push --bookmark "${BRANCH}"
```

### Step 5 — Check Resolution and Auto-Rebase

After processing all comments:

```bash
# Re-check PR + statuses
bin/simple itf bb status "${PR_ID}" --ready-check
READY_RC=$?
```

If `READY_RC == 0` (ready to merge):

```bash
# Rebase onto latest main
jj git fetch
jj rebase -d main@origin

# Push rebased branch
jj git push --bookmark "${BRANCH}"

# Optionally auto-merge (ask user first in single-pass mode)
# bin/simple itf bb merge "${PR_ID}" --strategy squash
```

### Step 6 — Report

Print:
- PR id and final state (`OPEN`, `MERGED`, etc.)
- Comments processed (count of CODE_FIX / QUESTION / NIT / APPROVAL)
- Whether auto-merge fired
- Any unresolved blockers (failed status checks, pending reviewers)

## Post-Merge Cleanup

After merge:

```bash
jj bookmark delete "${BRANCH}"
```

## Bot Approval (called from review_loop L2)

When the orchestrator's bot-reviewer verdict is `approve`, this skill is
invoked with `--bot-approve`:

```bash
bin/simple itf bb approve "${PR_ID}"
```

`request-changes` from the bot routes back to Step 3 with new comments.

## Error Handling

| Error                              | Action                                       |
|------------------------------------|----------------------------------------------|
| `blocked-auth: 401/403`            | Re-run `bb_setup`                            |
| `403` on `bb merge`                | Branch policy / required reviewers; surface to user |
| `409` on `bb merge`                | PR not mergeable (conflicts); rebase + retry |
| `not found 404`                    | PR id wrong or PR was deleted                |
| `429`                              | Respect `Retry-After`; back off              |
