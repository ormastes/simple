# SPipe Phase 6: Refactor -- Tech Lead

**Role:** Tech Lead -- Refactor for quality: deduplication, file splitting, clean code
**Blinders:** ONLY code quality. No new features, no behavior changes.
**Context budget:** sub-40% -- load only implementation files + their specs.

## State

- **Read:** `.spipe/<feature>/state.md` -- get impl file paths from Phase 5
- **Write:** `.spipe/<feature>/state.md` -- update with refactor status

## Entry Criteria

- State file exists with `phase: implement` marked complete
- All specs passing (verified in Phase 5)
- Implementation files listed under `impl_files:` in state

## Process

1. Read `.spipe/<feature>/state.md` to get implementation file paths
2. Run duplication check: `bin/simple duplicate-check <impl-file-or-dir>` for each implementation scope
3. Run linter: `bin/simple build lint` on impl files
4. For each issue found (max 10 refactor-test cycles total; stop after 10 even if issues remain):
   a. **Duplication:** Extract shared logic into helper functions
   b. **Large files/classes (>800 lines):** Split by methodology — (1) try to
      extract a real class first; (2) divide by the semantic of the class
      description; (3) cut along the lowest-coupling / highest-cohesion seam
      (confirm with LCOM/CBO/fan-out); (4) name each piece by meaning. Use the
      highest-capability model to decide (or review+accept) the division and
      record which model decided it.
   c. **`_ClassName/` folder:** When splitting one class, move the pieces into a
      `_ClassName/` folder (leading `_` = transparent package; files resolve as
      if in the parent, siblings still see the class with no new `use`). Move
      existing numbered splits into `_ClassName/` and rename by semantic meaning.
      Never `*_1`, `*_2`, `part1`, `ver1`, `v1`, or numbered copy/version names.
   d. **Dead code:** Remove unused functions, imports, variables
5. After EVERY change, run specs to verify no behavior change:
   `set -o pipefail; bin/simple test <spec_file> 2>&1 | tail -40` for each spec from Phase 4
   If a refactor breaks specs, revert that change and note it in state file — do NOT loop trying to fix it
6. Run `.claude/skills/spipe_doc_wiki_refactor.md` for any docs, wiki-style process knowledge, feature/layer expert links, stale command names, or stale file paths affected by the implementation
7. If workflow/tooling, evidence wrappers, generated spec shape, or
   verification contracts changed, confirm matching `doc/07_guide`,
   `doc/06_spec`, `.codex/skills/`, `.agents/skills/`, `.claude/skills/`,
   `.claude/agents/spipe/`, and `.gemini/commands/` instructions were refreshed
   or record `N/A` in the state file.
8. Run numbered artifact guard:
   `sh scripts/audit/numbered-artifact-guard.shs --working`
   `sh scripts/audit/numbered-artifact-guard.shs --staged`
9. Run final lint pass: `set -o pipefail; bin/simple build lint 2>&1 | tail -30`
10. Update state file with refactor status and doc/wiki refactor status

## Rules

- **No behavior changes:** Specs must pass identically before and after
- **Run specs after every change:** One refactor at a time, test after each
- **File size limit:** Split any file exceeding 800 lines
- **Duplication threshold:** Extract any logic duplicated 3+ times
- **Naming conventions:** Follow existing project patterns (snake_case functions, PascalCase types)
- **No new features:** Do not add functionality, only restructure
- **Docs are hygiene only:** Doc/wiki refactoring may fix stale links and process references, but must not introduce new product scope
- **No numbered split names:** Do not create `foo_1`, `foo_2`, `part1`,
  `ver1`, `v1`, or equivalent files when updating or splitting existing code

## Boil a Small Lake

Pick ONE refactoring issue. Fix it. Run specs. Move to the next.
Do not attempt a grand restructuring. Small, safe, incremental changes.
If a refactoring risks breaking behavior, skip it and note in state file.

## Exit Criteria

- [ ] No duplications reported by `bin/simple duplicate-check <impl-file-or-dir>`
- [ ] Lint clean: `bin/simple build lint` passes with no warnings
- [ ] No file exceeds 800 lines
- [ ] All specs still pass: `bin/simple test <spec_file>` green for each
- [ ] Doc/wiki refactor pass recorded in state file
- [ ] Process docs/skills/agent instructions refreshed or explicitly `N/A`
- [ ] Before/after structural diagram included when module boundaries changed (see `.claude/skills/lib/spipe_diagrams.md`)
- [ ] Numbered artifact guard passes
- [ ] State file updated: `phase: refactor` marked complete

## Output

- Cleaned implementation files (same paths or split into new modules)
- Updated `.spipe/<feature>/state.md`
