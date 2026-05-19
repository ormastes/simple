# SPipe State: smoke-test

## User Request
> verify deploy

## Refined Goal
> smoke

## Harness
- User Approved: true
- Prevent: allow
- Hook Providers: codex, claude, gemini
- Event Log: .spipe/smoke-test/events.jsonl

## Acceptance Criteria
- [x] AC-1: Common hook envelopes are normalized for Codex, Claude, and Gemini.
- [x] AC-2: Provider hooks feed one shared event log and gate path.
- [x] AC-3: The HUD shows model, jj worktree, commit, hours remaining, week remaining, and goal.
- [x] AC-4: Skill deploy output documents provider hook snippets.
- [x] AC-5: Prevention blocks when approval/state gates fail.
