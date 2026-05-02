# SPipe Review-Loop Dogfood Checklist — 2026-04-26

Scope:
- `tools/claude-plugin/repo-and-pull-req/agents/review_loop.md`
- `tools/claude-plugin/repo-and-pull-req/agents/review_loop_codex_first.md`
- `tools/claude-plugin/repo-and-pull-req/skills/git/gh_pull_req_review.md`

This is the execution checklist for the remaining issue #10 review-loop
dogfood work. It does not change the loop yet; it records the exact
evidence to capture during L2 and L3 real-PR runs and the gaps that should
be patched only after Outlook + daily-debug are proven end-to-end.

## Preconditions

- Use a toy PR with a tiny safe change (doc-only or comment-only).
- Record the PR number, branch name, target (`gh`), and requested level.
- Confirm `.review/<pr>/state.json` is created on first cycle.
- Confirm the scheduler cadence matches the level:
  - L2: every 60s, cap 24h / 1440 cycles.
  - L3: every 5m, cap 7d / 2016 cycles.

## L2 Checklist

- Start with:
  - `/schedule 60s /repo_and_pull_req review <pr-number> --level=2`
- Capture initial state file values:
  - `level=2`
  - `target=gh`
  - `status=watching` or `awaiting-bot`
  - `cycle_count=0`
- Verify the Codex-first reviewer path runs:
  - `approver` becomes `codex` or `claude`
  - `verdict_source` is set
  - `bot_approved=true` only after an `approve` verdict
- Verify state transitions in order:
  - `watching` -> `awaiting-bot`
  - `awaiting-bot` -> `awaiting-checks`
  - `awaiting-checks` -> `merged`
- Verify PR-side evidence:
  - bot approval appears in GitHub review history
  - checks are polled until green
  - merge is squash + delete branch
- Capture terminal or log evidence for blocked paths if they happen:
  - `blocked` for permission failure
  - `blocked-auth` for token/setup failure
  - `blocked-conflict` for merge conflict
- Confirm the schedule is removed on `merged`, `closed`, `max-cycles`, or any `blocked*` status.

## L3 Checklist

- Start with:
  - `/schedule 5m /repo_and_pull_req review <pr-number> --level=3`
- Capture initial state file values:
  - `level=3`
  - `bot_approved=false`
  - `human_approved=false`
- Verify no bot-approval occurs:
  - no `gh pr review --approve` action
  - `status=awaiting-human` after the review pass
- Apply a real human approval and capture:
  - `human_approved=true`
  - checks remain independently tracked
- Verify state transitions in order:
  - `watching` -> `awaiting-human`
  - `awaiting-human` -> `awaiting-checks`
  - `awaiting-checks` -> `merged`
- Verify merge only occurs after both conditions are true:
  - at least one human `APPROVED` review
  - checks passing

## Evidence To Save

- `.review/<pr>/state.json` snapshots:
  - first cycle
  - after bot verdict / human approval
  - just before merge
  - final merged state
- GitHub PR review timeline screenshots or copied event summaries.
- Scheduler entry creation and removal evidence.
- Merge command result summary and final PR state.

## Gaps Found

- The older plan referenced `tools/claude-plugin/repo-and-pull-req/agents/gh_pull_req_review.md`, but the actual file is `tools/claude-plugin/repo-and-pull-req/skills/git/gh_pull_req_review.md`.
- `review_loop.md` documents L1 as preserving historical opportunistic merge behavior, which intentionally differs from the architecture table’s simplified “comments only” summary. Dogfood should treat that as expected, not as a bug.
- The docs describe scheduler cancellation as `/repo_and_pull_req review stop <pr#>`, but the exact dispatcher hook should be validated during the first real run and patched only if the command name differs in practice.

## Minimal Patch Plan If Dogfood Exposes Problems

- If the stop hook name is wrong, patch only the review-loop docs to the real dispatcher command.
- If state fields are missing at runtime, patch state initialization in `review_loop.md` to match the documented schema.
- If GitHub review polling returns data in a different shape, patch `skills/git/gh_pull_req_review.md` examples without changing the L2/L3 state machine.
