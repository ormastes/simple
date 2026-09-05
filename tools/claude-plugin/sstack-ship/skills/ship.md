# SStack Phase 8: Ship Skill — Release Manager

**Self-sufficient.** Any LLM (Claude, Codex, Gemini) can run this phase independently. Does not depend on any other LLM having participated in prior steps.

VCS sync, documentation, completion report. No code changes.

## Usage

```
/ship                                # Ship from state file
/ship path/to/feature                # Ship specific feature
```

Argument: `$ARGUMENTS`

---

## Procedure

### Step 1 — Load State

1. Read `.sstack/<feature>/state.md` to get full pipeline summary
2. Verify `phase: verify` is marked complete
3. Verify no critical issues flagged

### Step 2 — Commit

1. Check VCS status: `jj status`
2. Compose commit message from state file summary:
   - Feature name and description
   - Key files added/modified
   - Test results summary
3. Commit all changes: `jj commit -m "<type>(<scope>): <description>"`

### Step 3 — Push

```
jj bookmark set main -r @-
jj git push --bookmark main
```

### Step 4 — Completion Report

Generate report at `doc/09_report/<feature>_complete_<date>.md`:

```markdown
# <Feature> -- Completion Report

**Date:** <YYYY-MM-DD>
**Pipeline:** SStack 8-phase

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

### Step 5 — Finalize State

Update `.sstack/<feature>/state.md`: mark `phase: ship` complete, `status: done`.

---

## Rules

- **No code changes:** If something is broken, send back to appropriate phase
- **Commit message format:** `feat(<scope>): <description>` for features, `fix(<scope>):` for fixes
- **Report must exist:** Do not skip the completion report
- **Push must succeed:** Verify push completes without errors
- **State file is source of truth:** Everything in the report comes from state
- **Context budget:** sub-40% — load only state file + VCS status

## Boil a Small Lake

Commit first. Push second. Write report third. Update state last.
Four steps, in order, no shortcuts. Each must succeed before the next.

---

## Exit Criteria

- [ ] Code committed: `jj log` shows new commit
- [ ] Code pushed: `jj git push` succeeded
- [ ] Completion report exists: `doc/09_report/<feature>_complete_<date>.md`
- [ ] State file updated: `phase: ship` marked complete, `status: done`

## Output

- Git commit on main
- Completion report at `doc/09_report/<feature>_complete_<date>.md`
- Final `.sstack/<feature>/state.md` with `status: done`
