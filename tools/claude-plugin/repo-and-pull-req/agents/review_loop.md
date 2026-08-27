# Review Loop Agent — Autonomous PR Review

## Role

Autonomous PR reviewer. Invoked on a schedule (cadence depends on `--level`)
to check PR status, process review comments, fix code or reply, and (per
`--level`) obtain scoped admission or an eligible independent provider
approval, then merge.

## Invocation

Via `/schedule` skill (cadence determined by `--level` — see *Per-Level
Procedure* below):

```
# L1 (default — one-shot, current behavior preserved)
/repo_and_pull_req review <pr-number>

# L2 (scoped admission/provider approval + merge; poll 60s up to 24h)
/schedule 60s /repo_and_pull_req review <pr-number> --level=2

# L3 (waits for eligible independent provider User account; poll 5m up to 7d)
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
  "user_account_approved": false,
  "self_review_admitted": false,
  "admission_dispatched": false,
  "admission_scope": null,
  "checks_passing": false,
  "merge_attempted": false,
  "cycle_count": 0,
  "last_check": "2026-04-10T12:00:00Z",
  "comments_processed": 0,
  "fixes_applied": 0,
  "status": "watching"
}
```

Status values: `watching` | `awaiting-bot` |
`awaiting-self-review-admission` | `awaiting-provider-user` |
`awaiting-checks` | `merged` | `closed` | `max-cycles` | `blocked` |
`blocked-conflict` | `blocked-auth` | `blocked-provider-approval` |
`blocked-self-review-admission`

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
  USER_ACCOUNT_APPROVED=$(jq -r '.user_account_approved // .human_approved // false' "$STATE_FILE")
  SELF_REVIEW_ADMITTED=$(jq -r '.self_review_admitted // false' "$STATE_FILE")
  ADMISSION_DISPATCHED=$(jq -r '.admission_dispatched // false' "$STATE_FILE")
  ADMISSION_SCOPE=$(jq -r '.admission_scope // "null"' "$STATE_FILE")
  CHECKS_PASSING=$(jq -r '.checks_passing // false' "$STATE_FILE")
  MERGE_ATTEMPTED=$(jq -r '.merge_attempted // false' "$STATE_FILE")
else
  CYCLE_COUNT=0
  LAST_CHECK="1970-01-01T00:00:00Z"
  LEVEL="${CLI_LEVEL:-1}"
  TARGET="${CLI_TARGET:-$DETECTED_TARGET}"
  APPROVER="null"
  BOT_APPROVED=false
  USER_ACCOUNT_APPROVED=false
  SELF_REVIEW_ADMITTED=false
  ADMISSION_DISPATCHED=false
  ADMISSION_SCOPE=null
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

If `verdict == approve`, preserve its exact head, reviewer model/effort, and
P0/P1 counts. For GitHub, compare stable provider actor and author IDs. An
independent credential may call the provider approval API. A same-author
credential must never do so: when the review is high-capability, effort is
`high|xhigh|max|ultra`, and P0/P1 are both zero, dispatch
`review-admission.yml` on `main` once for the exact head/base scope with
`PASS:0:0`. Otherwise set a terminal blocked status and cancel. Follow
`gh_pull_req_review.md` for the complete dispatch and invalidation contract.

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

#### L2 — Scoped admission/provider approval + merge (poll 60s up to 24h)

1. Run the review pass and exact-head bot verdict. Same-author GitHub
   credentials dispatch `SPipe Self Review Admission`; independent credentials
   may submit provider approval. Persist the dispatch scope and never redispatch
   it every cycle.
2. Poll required checks and the exact-head admission when dispatched.
   - If green → `CHECKS_PASSING=true`, `status=awaiting-checks` cleared.
   - If failing → cycle continues, `status=watching`.
   - Admission `failure`, `action_required`, cancellation, timeout, or skip →
     `status=blocked-self-review-admission`; save, comment once, cancel, exit.
     Push/base/PR/policy/ruleset changes and expiry require a fresh review and
     explicitly restarted dispatch.
3. If `(BOT_APPROVED || SELF_REVIEW_ADMITTED) && CHECKS_PASSING &&
   !MERGE_ATTEMPTED`:
   ```bash
   MERGE_ATTEMPTED=true
   gh pr merge "${PR_NUMBER}" --squash --delete-branch
   ```
   Status = `merged` on success; otherwise classify failure (see
   *Failure Modes*).

#### L3 — Wait for eligible independent provider user account

1. Run review pass (Step 3). Do not bot-approve. Set
   `status=awaiting-provider-user`.
2. Poll for an independent `APPROVED` review from a provider actor whose type
   is `User`, not a GitHub App/Bot. This account classification does not prove
   that a human operated it. Use the lookup in `gh_pull_req_review.md`, then set
   `USER_ACCOUNT_APPROVED=true`.
   ```bash
   # Resolve author, review actors, and each actor's provider type fail-closed.
   ```
3. Poll checks (same as L2).
4. If `USER_ACCOUNT_APPROVED && CHECKS_PASSING && !MERGE_ATTEMPTED`:
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
| 403  | `blocked`           | Post one comment ("Credential lacks permission"), save state, **cancel schedule, exit**. |
| 409  | `blocked-conflict`  | Post one comment ("Merge conflict — needs manual rebase"), save state, **cancel schedule, exit**. |
| 401  | `blocked-auth`      | Post one comment ("Bot token expired/invalid — re-run setup"), save state, **cancel schedule, exit**. |
| rejected provider approval | `blocked-provider-approval` | Same-author or ineligible/rejected provider approval: never retry; save, comment once, **cancel, exit**. |
| rejected/invalid admission | `blocked-self-review-admission` | Save exact scope/error, comment once, **cancel, exit**. |
| other nonzero API exit | `blocked` | Preserve diagnostics; do not retry an unclassified policy/auth failure. |

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
  --argjson user_app "$USER_ACCOUNT_APPROVED" \
  --argjson self_app "$SELF_REVIEW_ADMITTED" \
  --argjson admission_sent "$ADMISSION_DISPATCHED" \
  --arg admission_scope "$ADMISSION_SCOPE" \
  --argjson checks "$CHECKS_PASSING" \
  --argjson merged "$MERGE_ATTEMPTED" \
  --argjson cyc $((CYCLE_COUNT + 1)) \
  --arg now "$NOW" \
  --argjson cmts "$TOTAL_COMMENTS" \
  --argjson fixes "$TOTAL_FIXES" \
  --arg status "${STATUS:-watching}" \
  '{pr_number:$pr, branch:$br, jira_key:$jk, target:$target, level:$level,
    approver:$approver, verdict_source:$vsrc,
    bot_approved:$bot_app, user_account_approved:$user_app,
    self_review_admitted:$self_app, admission_dispatched:$admission_sent,
    admission_scope:$admission_scope,
    checks_passing:$checks, merge_attempted:$merged,
    cycle_count:$cyc, last_check:$now,
    comments_processed:$cmts, fixes_applied:$fixes,
    status:$status}' > "$STATE_FILE"
```

## Audit Trail (per arch §3-Level Review State Machine)

- `approver` records which review source produced the verdict (`codex` |
  `claude` | `provider-user`). `provider-user` is an account class, not proof
  of human operation.
- `verdict_source` records the agent name (e.g. `codex:rescue`,
  `claude:general-purpose`) for forensic traceability.
- The PR UI shows the token principal only when a provider review was posted.
  Same-author GitHub review instead produces an exact-head self-attested status
  check; `approver` names the reviewing model, not a provider approver.

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
| L2 done            | admission/provider approval + checks + merge → `merged` |
| L3 done            | eligible provider `User` approval + checks + merge → `merged` |

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
