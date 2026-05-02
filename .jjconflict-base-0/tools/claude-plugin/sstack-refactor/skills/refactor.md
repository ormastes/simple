# SStack Phase 6: Refactor Skill — Tech Lead

**Self-sufficient.** Any LLM (Claude, Codex, Gemini) can run this phase independently. Does not depend on any other LLM having participated in prior steps.

Refactor for quality: deduplication, file splitting, clean code. No behavior changes.

## Usage

```
/refactor                            # Refactor from state file
/refactor path/to/feature            # Refactor specific feature
```

Argument: `$ARGUMENTS`

---

## Procedure

### Step 1 — Load State

1. Read `.sstack/<feature>/state.md` to get impl file paths from Phase 5
2. Verify `phase: implement` is marked complete
3. Extract `impl_files:` and `spec_files:` lists

### Step 2 — Identify Issues

1. Run duplication check: `bin/simple duplicate-check` on impl files
2. Run linter: `bin/simple build lint` on impl files
3. Check file sizes — flag any file exceeding 800 lines

### Step 3 — Refactor Incrementally

For each issue found:

1. **Duplication:** Extract shared logic into helper functions
2. **Large files (>800 lines):** Split into focused modules
3. **Naming:** Ensure consistency with project conventions (snake_case functions, PascalCase types)
4. **Dead code:** Remove unused functions, imports, variables

After EVERY change, run specs to verify no behavior change:
`bin/simple test <spec_file>` for each spec from Phase 4

### Step 4 — Final Verification

1. Run final lint pass: `bin/simple build lint`
2. Verify all specs still pass
3. Update `.sstack/<feature>/state.md` with refactor status

---

## Rules

- **No behavior changes:** Specs must pass identically before and after
- **Run specs after every change:** One refactor at a time, test after each
- **File size limit:** Split any file exceeding 800 lines
- **Duplication threshold:** Extract any logic duplicated 3+ times
- **Naming conventions:** Follow existing project patterns
- **No new features:** Do not add functionality, only restructure
- **Context budget:** sub-40% — load only implementation files + their specs

## Boil a Small Lake

Pick ONE refactoring issue. Fix it. Run specs. Move to the next.
Do not attempt a grand restructuring. Small, safe, incremental changes.
If a refactoring risks breaking behavior, skip it and note in state file.

---

## Exit Criteria

- [ ] No duplications reported by `bin/simple duplicate-check`
- [ ] Lint clean: `bin/simple build lint` passes with no warnings
- [ ] No file exceeds 800 lines
- [ ] All specs still pass: `bin/simple test <spec_file>` green for each
- [ ] State file updated: `phase: refactor` marked complete

## Output

- Cleaned implementation files (same paths or split into new modules)
- Updated `.sstack/<feature>/state.md`
