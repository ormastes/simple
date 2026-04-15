# Review Loop Agent — Autonomous PR Review

## Role

Autonomous PR reviewer. Invoked on a schedule (hourly) to check PR status,
process review comments, fix code or reply, and auto-rebase when resolved.

## Invocation

Via `/schedule` skill:
```
/schedule 1h /repo_and_pull_req review <pr-number>
```

Or directly for a single pass:
```
/repo_and_pull_req review <pr-number>
```

## State Management

State persisted in `.review/<pr-number>/state.json`:

```json
{
  "pr_number": 42,
  "branch": "pr/add-repo-plugin",
  "jira_key": "SIMPLE-42",
  "cycle_count": 0,
  "last_check": "2026-04-10T12:00:00Z",
  "comments_processed": 0,
  "fixes_applied": 0,
  "status": "watching"
}
```

Status values: `watching` | `merged` | `closed` | `max-cycles`

## Procedure per Cycle

### 1. Load State

```bash
STATE_FILE=".review/${PR_NUMBER}/state.json"
mkdir -p ".review/${PR_NUMBER}"
if [ -f "$STATE_FILE" ]; then
  # Read existing state
  CYCLE_COUNT=$(jq -r .cycle_count "$STATE_FILE")
  LAST_CHECK=$(jq -r .last_check "$STATE_FILE")
else
  # First run — initialize
  CYCLE_COUNT=0
  LAST_CHECK="1970-01-01T00:00:00Z"
fi
```

### 2. Check Exit Conditions

- If `CYCLE_COUNT >= 24`: set status="max-cycles", notify user, exit
- Check PR state: `gh pr view ${PR_NUMBER} --json state`
  - If MERGED: set status="merged", run post-merge cleanup, exit
  - If CLOSED: set status="closed", exit

### 3. Run GitHub Review Pass

Read and follow `skills/git/gh_pull_req_review.md`:
- Fetch comments newer than `LAST_CHECK`
- Classify and process each comment
- Fix code, reply to questions, apply nits
- Push fixes if any

### 4. Run Jira Review Pass (if configured)

Check if Jira issue is linked:
- If yes: read and follow `skills/jira/jira_pull_req_review.md`
- Process Jira-side comments
- Update Jira status

### 5. Check Auto-Merge Conditions

After processing all comments:

```bash
DECISION=$(gh pr view "${PR_NUMBER}" --json reviewDecision --jq .reviewDecision)

if [ "$DECISION" = "APPROVED" ]; then
  # All resolved + approved → rebase and merge
  jj git fetch
  jj rebase -d main@origin

  # File count guard
  FILE_COUNT=$(git ls-files | wc -l | tr -d ' ')

  # Push rebased branch
  jj git push --bookmark "${BRANCH}"

  # Auto-merge
  gh pr merge "${PR_NUMBER}" --rebase --delete-branch

  # Post-merge cleanup
  jj git fetch
  jj rebase -d main@origin
  jj bookmark delete "${BRANCH}" 2>/dev/null || true

  # Update state
  STATUS="merged"
fi
```

### 6. Save State

```bash
NOW=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
cat > "$STATE_FILE" <<EOF
{
  "pr_number": ${PR_NUMBER},
  "branch": "${BRANCH}",
  "jira_key": "${JIRA_KEY:-null}",
  "cycle_count": $((CYCLE_COUNT + 1)),
  "last_check": "${NOW}",
  "comments_processed": ${TOTAL_COMMENTS},
  "fixes_applied": ${TOTAL_FIXES},
  "status": "${STATUS:-watching}"
}
EOF
```

## Context Budget

Sub-40%. Each cycle is a fresh agent invocation — no accumulated context.
Load only: state file, PR comments, specific code files mentioned in comments.

## Exit Conditions

| Condition | Action |
|-----------|--------|
| PR merged | Clean up bookmark + state, report success |
| PR closed | Clean up state, report closure |
| 24 cycles reached | Stop schedule, notify user |
| All approved | Auto-rebase, merge, clean up |

## Conflict Resolution

If rebase has conflicts:

1. Identify conflicting files from `jj st`
2. Read both versions (ours and theirs)
3. Resolve conflicts programmatically
4. Commit resolution: `jj commit -m "fix: resolve merge conflict"`
5. Push: `jj git push --bookmark "${BRANCH}"`
6. If conflict is too complex: add PR comment asking for human help, continue watching
