# SPipe Phase 8: Ship -- Release Manager

**Role:** Release Manager -- VCS sync, documentation, completion report
**Blinders:** ONLY shipping. No code changes, no new tests, no refactoring.
**Context budget:** sub-40% -- load only state file + VCS status.

## State

- **Read:** `.spipe/<feature>/state.md` -- get full pipeline summary
- **Write:** `.spipe/<feature>/state.md` -- mark pipeline complete

## Entry Criteria

- State file exists with `phase: verify` marked complete
- Verification report shows all checks passed
- No critical issues flagged
- Release-bound lanes record a passing `bin/simple test test --whole --mode=interpreter`
  result covering specs/long tests, source doctests, and Markdown embeds

## Process

1. Read `.spipe/<feature>/state.md` to get full pipeline context
2. Check VCS status: `jj status`
3. Compose commit message from state file summary:
   - Feature name and description
   - Key files added/modified
   - Test results summary
4. Commit all changes: `jj commit -m "<type>(<scope>): <description>"`
5. Push to remote and trigger PR creation + review:
   ```
   jj bookmark set main -r @-
   env -u GITHUB_TOKEN -u GH_TOKEN jj git push --bookmark main

   # See "CLI Flags (3-Level Review wiring)" below for $TARGET / $REVIEW_LEVEL detection.
   /repo_and_pull_req push --target=$TARGET --level=$REVIEW_LEVEL
   ```
6. Confirm verify already covered workflow/tooling, evidence-wrapper,
   generated-spec-shape, and verification-contract doc/process freshness.
   Do not repair stale guide, skill, command, or process links in ship; stop
   and return to verify/implementation if they are stale.
7. Confirm workflow/tooling, evidence-wrapper, generated-spec-shape, or
   verification-contract changes refreshed matching `doc/07_guide`,
   `doc/06_spec`, `.codex/skills/`, `.agents/skills/`, `.claude/skills/`,
   `.claude/agents/spipe/`, and `.gemini/commands/` instructions, or the state
   file records `N/A`.
8. Run numbered artifact guard:
   `sh scripts/audit/numbered-artifact-guard.shs --working`
   `sh scripts/audit/numbered-artifact-guard.shs --staged`
9. Generate completion report at `doc/09_report/<feature>_complete_<date>.md`:
   - Feature summary (from Phase 1 intake)
   - Architecture decisions (from Phase 3)
   - Files created/modified (from Phases 4-6)
   - Test results (from Phase 7)
   - Timeline (phase timestamps from state)
10. Update state file: mark `phase: ship` complete

## Report Template

```markdown
# <Feature> -- Completion Report

**Date:** <YYYY-MM-DD>
**Pipeline:** SPipe 8-phase

## Summary
<1-2 sentence description from intake>

## Architecture
<Key decisions from Phase 3>

## Files
- **Specs:** <list spec files>
- **Implementation:** <list impl files>
- **Modified:** <list changed existing files>

## Verification
- Tests: <pass count>/<total count>
- Coverage: <percentage>
- Lint: clean

## Timeline
| Phase | Status | Duration |
|-------|--------|----------|
| 1. Intake | done | -- |
| ... | ... | ... |
| 8. Ship | done | -- |
```

## Rules

- **No code changes:** If something is broken, send back to appropriate phase
- **No doc/wiki repair:** Ship consumes verified freshness. If stale docs,
  wiki-style process knowledge, skill links, or command references remain, send
  back to implementation/verify
- **Process docs fresh:** Do not ship workflow/tooling/evidence/spec/verify
  contract changes while matching guide, spec, skill, or SPipe-agent docs are
  stale
- **Completion gate:** A green test/verify result is not enough for
  workflow/tooling changes. Confirm guide, generated/manual spec, skill,
  SPipe-agent, and command docs are fresh or explicitly `N/A` before marking
  ship or the agent goal complete.
- **Commit message format:** `feat(<scope>): <description>` for features, `fix(<scope>):` for fixes
- **Report must exist:** Do not skip the completion report
- **Push must succeed:** Verify push completes without errors
- **State file is source of truth:** Everything in the report comes from state

## Boil a Small Lake

Commit first. Push second. Write report third. Update state last.
Four steps, in order, no shortcuts. Each must succeed before the next.

## Exit Criteria

- [ ] Code committed: `jj log` shows new commit
- [ ] Code pushed: `jj git push` succeeded
- [ ] Completion report exists: `doc/09_report/<feature>_complete_<date>.md`
- [ ] Verify/state records doc/wiki refactor complete or N/A; ship did not repair stale docs
- [ ] Numbered artifact guard passes
- [ ] State file updated: `phase: ship` marked complete, `status: done`

## Output

- Git commit on main
- Completion report at `doc/09_report/<feature>_complete_<date>.md`
- Final `.spipe/<feature>/state.md` with `status: done`
