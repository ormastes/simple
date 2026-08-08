# /dev

Development command for quick iteration and testing.

## Usage
```
/dev [task_description]
```

## Purpose
Fast development loop for incremental changes without full pipeline overhead.

## When to use
- Small bug fixes
- Quick feature iterations
- Experimental changes

## Notes
This is a lightweight development shortcut. For production work, use the full pipeline: /research → /design → /impl → /verify → /release

"Lightweight" means fewer PHASES, not a lower bar for landing. Anything that
reaches `main` carries the same knowledge and evidence obligations as work that
went through the full pipeline — see the final step check below.

## Final Step Check (definition of done)

**Run this before you say the task is done, and again before any commit.**
It is a checklist, not a suggestion: state each line's verdict explicitly.
A line that does not apply is answered `N/A — <reason>`, never skipped silently.

### 1. Evidence
- [ ] Every claim of "works" is backed by a measured number you ran yourself,
      not a subagent's report relayed unverified.
- [ ] Tests: only the final `Results:` line and the exit code are authoritative
      (output is flooded with lint/gc warnings — GREP the verdict, never `tail`).
- [ ] **Sabotage-probe each behavioural change**: break the implementation,
      confirm RED, revert, confirm GREEN. Report all three numbers.
      A test that cannot fail proves nothing.
- [ ] If two changes could each explain a passing test, ISOLATE which one does.
- [ ] `bin/simple lint <changed files>` → 0 errors.
- [ ] No sabotage/probe residue or scratch files left in the repo.

### 2. Knowledge updates — the step most often skipped
Ask for EACH: "did this change what a future reader/agent needs to know?"
If yes, update it in the SAME change as the work.
- [ ] `doc/` — research/architecture/design/plan for the area touched.
- [ ] `doc/07_guide/` — the developer-facing guide. **Never let a guide claim a
      capability works if it is not reachable through the binary users actually
      run.** State the blocker instead.
- [ ] `doc/00_llm_process/feature_expert/<feature>/skill.md` and
      `doc/00_llm_process/layer_expert/<layer>/skill.md` — REQUIRED by
      `.claude/rules/vcs.md`, which says to commit the wiki update in the same
      change as the work it describes. Create the entry if none covers the area.
      Templates: `.spipe/spipe/doc/00_llm_process/template/{feature,layer}_skill.md`.
- [ ] `.claude/skills/`, `.claude/agents/spipe/`, `.claude/commands/`,
      `.codex/skills/`, `.agents/skills/`, `.gemini/commands/` — if the way we
      WORK changed (a new practice, trap, or verification step), not just the code.
- [ ] `doc/08_tracking/bug/` — file a record for every gap found and NOT fixed,
      with file:line and the unblock condition. Never convert a TODO to a NOTE.

### 3. Honesty
- [ ] Say plainly what did NOT get done, what stayed RED, and what was reverted.
- [ ] A correctly-reverted change (found to be unreachable/dead) and a
      well-evidenced "this can't work yet, here's why" are SUCCESSES — report
      them as such rather than hiding them.
- [ ] If a claim you made earlier turned out wrong, correct it explicitly.

### 4. Landing
- [ ] Commit scoped to paths THIS session authored — never a whole-WC snapshot.
- [ ] Shared working copy? Another session may be mid-flight. Check
      `git status` for files you did not touch; a live `.git/index.lock` must be
      WAITED OUT, never deleted (see `.claude/rules/vcs.md`).
- [ ] Before landing a file someone else also edited, diff BOTH directions and
      confirm your copy is a forward delta that reverts nothing.
- [ ] After pushing, VERIFY: `git merge-base --is-ancestor <sha> origin/main`
      plus a tree-integrity check. A clean push exit is not proof.
