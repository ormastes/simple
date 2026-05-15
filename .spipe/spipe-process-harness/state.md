# SPipe State: spipe-process-harness

## User Request
> make spipe production level process harness; common hooks for Codex, Claude, Gemini; skill deploy infra; CLI HUD with model, jj worktree, commit, hours remaining, week remaining; goal state; prevention gate; commit pull rebase push.

## Refined Goal
> Provide shared SPipe hook, deploy, HUD, goal-state, and prevention infrastructure for Codex, Claude, and Gemini.

## Harness
- User Approved: true
- Prevent: allow
- Hook Providers: codex, claude, gemini
- Event Log: .spipe/spipe-process-harness/events.jsonl

## Acceptance Criteria
- [x] AC-1: Common hook envelopes are normalized for Codex, Claude, and Gemini.
- [x] AC-2: Provider hooks feed one shared event log and gate path.
- [x] AC-3: The HUD shows model, jj worktree, commit, hours remaining, week remaining, and goal.
- [x] AC-4: Skill deploy output documents provider hook snippets.
- [x] AC-5: Prevention blocks when approval/state gates fail.

