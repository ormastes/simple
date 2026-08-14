# /dev (compatibility alias)

`/dev` is no longer a separate lightweight workflow. Route requests to
`/sp_dev` and follow `.claude/skills/spipe.md`.

## Usage
```
/dev [task_description]
```

## Purpose
Compatibility only. It must not lower evidence, documentation, or verification
requirements relative to `/sp_dev`.

## Notes
This alias runs the same SPipe phases and completion gates as `/sp_dev`; it is
not a reduced-evidence shortcut.

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

### 5. SAML — only when a `.saml` file changed
Skip this section entirely otherwise; do not answer it `N/A` on unrelated work.

Run it with (note: `bin/simple saml ...` does NOT work — the Rust seed's argv
parser never consults the Simple dispatch table):

```bash
bin/simple run src/app/saml/main.spl analyze <file.saml>   # the evidence: lines
bin/simple run src/app/saml/main.spl check   <file.saml>   # rc=1 on errors
bin/simple run src/app/saml/main.spl doc --out <dir> <file.saml>
```

- [ ] Regenerated the analysis (`emit_analysis_report`) and the generated manual
      (`emit_markdown_manual`) from the edited source, and committed the manual
      alongside it. Both render from the same record on purpose — never
      hand-edit a file carrying the generated banner, and never let the manual
      lag the source it projects.
- [ ] Read the per-function `evidence:` line. `unevidenced` or `examples_only`
      is an UNFINISHED deliverable, not a warning to note and move past — the
      same bar as a RED test. Say which functions are still on those rungs.
- [ ] Every `llm fn` you touched carries a `# counter-example:`, so its state is
      `red_proven`. This is the sabotage probe (§1) expressed in the language:
      positive examples alone cannot show the oracle can fail. `tested` with no
      counter-example is not done.
- [ ] `errors=` is 0 and each remaining `!` warning is either fixed or filed
      with file:line under `doc/08_tracking/bug/`.
- [ ] `red_proven` today means a counter-example is *declared*, not observed to
      fail — examples are counted, not executed. Do not report it as proof.
      See `doc/01_research/infra/llm/saml_ergonomics_research_2026-08-10.md`.
- [ ] Coverage discovered from `test/**/*_spec.spl` (via `--specs DIR` /
      MCP `spec_dir`, landed 2026-08-10) counts toward `tested` and shows as
      an `external:<path>:<it_title>` entry in `tests=[...]`, but it can
      **never** raise a function to `red_proven` — that rung still requires
      an in-file `# counter-example:`. Do not credit a function as fully
      proven just because `--specs` found an external test; if it has no
      counter-example, `E-SAML-1810` will say so.
