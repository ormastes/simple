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
- [ ] AC-1: Common hook envelopes are normalized for Codex, Claude, and Gemini.
- [ ] AC-2: Provider hooks feed one shared event log and gate path.
- [ ] AC-3: The HUD shows model, jj worktree, commit, hours remaining, week remaining, and goal.
- [ ] AC-4: Skill deploy output documents provider hook snippets.
- [ ] AC-5: Prevention blocks when approval/state gates fail.
