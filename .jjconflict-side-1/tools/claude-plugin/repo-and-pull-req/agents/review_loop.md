# Review Loop Agent — Autonomous PR Review

## Role

Autonomous PR reviewer. Invoked on a schedule (cadence depends on `--level`)
to check PR status, process review comments, fix code or reply, and (per
`--level`) bot-approve / wait for human approval / merge.

## Invocation

Via `/schedule` skill (cadence determined by `--level` — see *Per-Level
Procedure* below):

```
# L1 (default — one-shot, current behavior preserved)
/repo_and_pull_req review <pr-number>

# L2 (bot-approves + auto-merges; poll 60s up to 24h)
/schedule 60s /repo_and_pull_req review <pr-number> --level=2

# L3 (waits for human approval + merges; poll 5m up to 7d)
/schedule 5m /repo_and_pull_req review <pr-number> --level=3
```

Flags:
- `--level=1|2|3` (default: `1`)
- `--target=gh|bb` (default: detect from `git remote get-url origin`)

`--target=jira` is **not valid for L2/L3**; reject with clear error and
exit non-zero. L1 + Jira is delegated to the existing Jira sub-skill from
the dispatcher.

## State Management

State persisted in `.review/<pr-number>/state.json` (extended schema —
older state files are forward-compatible; missing keys take the defaults
listed in *Step 1*):

```json
{
  "pr_number": 42,
  "branch": "pr/add-repo-plugin",
  "jira_key": "SIMPLE-42",
  "target": "gh",
  "level": 1,
  "approver": "codex",
  "verdict_source": "codex:rescue",
  "bot_approved": false,
  "human_approved": false,
  "checks_passing": false,
  "merge_attempted": false,
  "cycle_count": 0,
  "last_check": "2026-04-10T12:00:00Z",
  "comments_processed": 0,
  "fixes_applied": 0,
  "status": "watching"
}
```

Status values: `watching` | `awaiting-bot` | `awaiting-human` |
`awaiting-checks` | `merged` | `closed` | `max-cycles` |
`blocked` | `blocked-conflict` | `blocked-auth`

Any `blocked*` status MUST cancel the `/schedule` entry — see
*Failure Modes* below. The bot must NEVER tight-loop on auth/policy
errors.

## Procedure per Cycle

### 1. Load State (with backward-compatible defaults)

```bash
STATE_FILE=".review/${PR_NUMBER}/state.json"
mkdir -p ".review/${PR_NUMBER}"

# Detect target from origin if not in state and not on CLI
DETECTED_TARGET=$(git remote get-url origin 2>/dev/null | \
  awk '/github\.com/{print "gh"; exit} /bitbucket\.org/{print "bb"; exit}')
DETECTED_TARGET="${DETECTED_TARGET:-gh}"

if [ -f "$STATE_FILE" ]; then
  # Use jq default-fallback form ( // ) so older state files still load.
  CYCLE_COUNT=$(jq -r '.cycle_count // 0'           "$STATE_FILE")
  LAST_CHECK=$(jq  -r '.last_check  // "1970-01-01T00:00:00Z"' "$STATE_FILE")
  LEVEL=$(jq       -r ".level // ${CLI_LEVEL:-1}"   "$STATE_FILE")
  TARGET=$(jq      -r ".target // \"${CLI_TARGET:-$DETECTED_TARGET}\"" "$STATE_FILE")
  APPROVER=$(jq    -r '.approver // "null"'         "$STATE_FILE")
  BOT_APPROVED=$(jq -r '.bot_approved   // false'   "$STATE_FILE")
  HUMAN_APPROVED=$(jq -r '.human_approved // false' "$STATE_FILE")
  CHECKS_PASSING=$(jq -r '.checks_passing // false' "$STATE_FILE")
  MERGE_ATTEMPTED=$(jq -r '.merge_attempted // false' "$STATE_FILE")
else
  CYCLE_COUNT=0
  LAST_CHECK="1970-01-01T00:00:00Z"
  LEVEL="${CLI_LEVEL:-1}"
  TARGET="${CLI_TARGET:-$DETECTED_TARGET}"
  APPROVER="null"
  BOT_APPROVED=false
  HUMAN_APPROVED=false
  CHECKS_PASSING=false
  MERGE_ATTEMPTED=false
fi
```

CLI flags override state (`--level=N`, `--target=X`) but the override is
written back so subsequent cycles agree.

### 2. Check Exit Conditions (cycle caps per level)

| Level | Cycle cadence | Hard stop      | Cycle cap          |
|-------|---------------|----------------|--------------------|
| L1    | one-shot      | n/a            | 1                  |
| L2    | poll 60s      | 24h            | 1440               |
| L3    | poll 5m       | 7d             | 2016               |

```bash
case "$LEVEL" in
  1) MAX_CYCLES=1    ;;
  2) MAX_CYCLES=1440 ;;
  3) MAX_CYCLES=2016 ;;
esac
if [ "$CYCLE_COUNT" -ge "$MAX_CYCLES" ]; then
  STATUS="max-cycles"; save_state; cancel_schedule; exit 0
fi

PR_STATE=$(gh pr view "${PR_NUMBER}" --json state --jq .state)
case "$PR_STATE" in
  MERGED) STATUS="merged"; cleanup; save_state; cancel_schedule; exit 0 ;;
  CLOSED) STATUS="closed"; save_state; cancel_schedule; exit 0 ;;
esac
```

### 3. Run Review Pass (per target)

For `target=gh`: read and follow
`skills/git/gh_pull_req_review.md` (which itself branches on `--level`).
For `target=bb`: read and follow
`skills/bb/bb_pull_req_review.md` (Agent C scope).

Both sub-skills:
- Fetch comments newer than `LAST_CHECK`
- Classify and process each comment
- Fix code, reply to questions, apply nits
- Push fixes if any

### 4. Run Jira Side-Pass (linkage only)

If a Jira key is linked, follow
`skills/jira/jira_pull_req_review.md` for **comment exchange only** —
Jira does not gate L2/L3 merge. (Per arch doc Q3: Jira is for ticket
linking; L2/L3 merge logic lives on gh/bb.)

### 5. Bot-Reviewer Verdict (L2 only)

For `LEVEL == 2`: dispatch the Codex-first / Claude-fallback bot
reviewer described in `agents/review_loop_codex_first.md`. Capture:

- `verdict ∈ {approve, request-changes, comment}`
- `approver ∈ {codex, claude}` (which agent produced it)
- `verdict_source` (e.g. `codex:rescue`, `claude:general-purpose`)

Record `approver` and `verdict_source` in state — this is the
audit-trail key the PR UI uses to attribute the action to the bot's
token-principal.

If `verdict == approve`: call the approve API for the target (see
`gh_pull_req_review.md` / `bb_pull_req_review.md`), set
`bot_approved=true`, `status=awaiting-checks`.

If `verdict == request-changes`: post inline comments (handled by
sub-skill), set `bot_approved=false`, status stays `watching`.

If `verdict == comment`: same as `request-changes` but no merge gate
flip; cycle continues.

### 6. Per-Level Auto-Merge Logic

#### L1 — One-shot review (current behavior preserved)

Only step run: comment processing + opportunistic merge if the PR is
**already** `APPROVED` at check time. No bot-approve, no polling, no
checks-wait. This deviates from the arch doc table (which lists L1 as
"comments only") to preserve the existing single-pass behavior — see
*Compatibility note* at the bottom of this section.

```bash
DECISION=$(gh pr view "${PR_NUMBER}" --json reviewDecision --jq .reviewDecision)
if [ "$DECISION" = "APPROVED" ]; then
  jj git fetch
  jj rebase -d main@origin
  FILE_COUNT=$(git ls-files | wc -l | tr -d ' ')
  jj git push --bookmark "${BRANCH}"
  gh pr merge "${PR_NUMBER}" --rebase --delete-branch
  STATUS="merged"
fi
```

#### L2 — Bot approves + auto-merges (poll 60s up to 24h)

1. Run review pass (Step 3) and bot-verdict (Step 5).
2. After bot-approve, poll checks: `gh pr checks ${PR_NUMBER} --json state`.
   - If green → `CHECKS_PASSING=true`, `status=awaiting-checks` cleared.
   - If failing → cycle continues, `status=watching`.
3. If `BOT_APPROVED && CHECKS_PASSING && !MERGE_ATTEMPTED`:
   ```bash
   MERGE_ATTEMPTED=true
   gh pr merge "${PR_NUMBER}" --squash --delete-branch
   ```
   Status = `merged` on success; otherwise classify failure (see
   *Failure Modes*).

#### L3 — Wait for human approval + merge (poll 5m up to 7d)

1. Run review pass (Step 3). Do NOT bot-approve. Set
   `status=awaiting-human`.
2. Poll for human approval:
   ```bash
   HUMAN=$(gh pr view "${PR_NUMBER}" --json reviews \
     --jq '[.reviews[] | select(.state=="APPROVED")] | length')
   if [ "$HUMAN" -gt 0 ]; then HUMAN_APPROVED=true; fi
   ```
3. Poll checks (same as L2).
4. If `HUMAN_APPROVED && CHECKS_PASSING && !MERGE_ATTEMPTED`:
   merge via `gh pr merge ${PR_NUMBER} --squash --delete-branch`.

#### Compatibility note (L1 vs arch doc)

The arch doc *3-Level Review State Machine* table lists L1 as
"post comments only — no merge." The existing `review_loop.md` already
auto-rebases and merges when the PR is APPROVED on the cycle. To meet
AC#1 ("never break existing behavior"), L1 here = **comments + merge
ONLY IF already APPROVED at check time** (no polling, no bot
approve). This is an intentional, documented deviation; treat the arch
doc as describing the L2/L3 escalation surface, not deprecating L1's
opportunistic merge.

### 7. Failure Modes (per arch §3-Level Review State Machine)

For any merge or approve API call, capture HTTP status. With `gh`,
either use `gh api --include` and grep `^HTTP/` for the code, or check
stderr for `HTTP 4xx`. Map:

| HTTP | Status field        | Action                                                         |
|------|---------------------|----------------------------------------------------------------|
| 403  | `blocked`           | Post one comment ("Bot lacks merge permission — please merge manually"), save state, **cancel schedule, exit**. |
| 409  | `blocked-conflict`  | Post one comment ("Merge conflict — needs manual rebase"), save state, **cancel schedule, exit**. |
| 401  | `blocked-auth`      | Post one comment ("Bot token expired/invalid — re-run setup"), save state, **cancel schedule, exit**. |

`cancel_schedule()` is shorthand for the dispatcher's stop hook:
`/repo_and_pull_req review stop <pr#>` — that's the actual mechanism
that removes the `/schedule` entry re-invoking this agent. Once
`blocked*`, the bot does not re-attempt; the human must unblock and
restart the loop manually. This implements the "NEVER tight-loop on
auth/policy errors" rule. `cleanup` is shorthand for "delete bookmark
+ post-merge `jj rebase -d main@origin`" (see *Conflict Resolution*
below for the rebase recipe).

### 8. Save State

```bash
NOW=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
jq -n \
  --argjson pr "$PR_NUMBER" \
  --arg br "$BRANCH" \
  --arg jk "${JIRA_KEY:-null}" \
  --arg target "$TARGET" \
  --argjson level "$LEVEL" \
  --arg approver "$APPROVER" \
  --arg vsrc "${VERDICT_SOURCE:-null}" \
  --argjson bot_app "$BOT_APPROVED" \
  --argjson hum_app "$HUMAN_APPROVED" \
  --argjson checks "$CHECKS_PASSING" \
  --argjson merged "$MERGE_ATTEMPTED" \
  --argjson cyc $((CYCLE_COUNT + 1)) \
  --arg now "$NOW" \
  --argjson cmts "$TOTAL_COMMENTS" \
  --argjson fixes "$TOTAL_FIXES" \
  --arg status "${STATUS:-watching}" \
  '{pr_number:$pr, branch:$br, jira_key:$jk, target:$target, level:$level,
    approver:$approver, verdict_source:$vsrc,
    bot_approved:$bot_app, human_approved:$hum_app,
    checks_passing:$checks, merge_attempted:$merged,
    cycle_count:$cyc, last_check:$now,
    comments_processed:$cmts, fixes_applied:$fixes,
    status:$status}' > "$STATE_FILE"
```

## Audit Trail (per arch §3-Level Review State Machine)

- `approver` records WHICH bot agent produced the verdict (`codex` |
  `claude` | `human`).
- `verdict_source` records the agent name (e.g. `codex:rescue`,
  `claude:general-purpose`) for forensic traceability.
- The PR UI shows the token-principal name (the bot account that owns
  the GitHub/Bitbucket token) — that's the entity that POSTed the
  approve. `approver` + `verdict_source` together let you tie the
  POSTer to the agent that decided.

## Context Budget

Sub-40%. Each cycle is a fresh agent invocation — no accumulated context.
Load only: state file, PR comments, specific code files mentioned in
comments.

## Exit Conditions

| Condition          | Action                                          |
|--------------------|-------------------------------------------------|
| PR merged          | Clean up bookmark + state, cancel schedule      |
| PR closed          | Clean up state, cancel schedule                 |
| Max cycles reached | `status=max-cycles`, cancel schedule, notify    |
| 401/403/409        | `status=blocked*`, post one comment, **cancel** |
| L1 + APPROVED      | Auto-rebase, merge, clean up                    |
| L2 done            | bot-approve + checks + merge → `merged`         |
| L3 done            | human-approve + checks + merge → `merged`       |

## Conflict Resolution

If rebase has conflicts:

1. Identify conflicting files from `jj st`
2. Read both versions (ours and theirs)
3. Resolve conflicts programmatically
4. Commit resolution: `jj commit -m "fix: resolve merge conflict"`
5. Push: `jj git push --bookmark "${BRANCH}"`
6. If conflict is too complex: set `status=blocked-conflict`, post one
   comment asking for human help, **cancel schedule** (do not keep
   polling on a conflict the bot can't fix).
