# SStack Phase 5: Implement Skill — Engineer (TDD)

**Self-sufficient.** Any LLM (Claude, Codex, Gemini) can run this phase independently. Does not depend on any other LLM having participated in prior steps.

Make failing specs pass using the Superpowers TDD pattern. Minimum viable code only.

## Usage

```
/implement                           # Implement from state file
/implement path/to/feature           # Implement specific feature
```

Argument: `$ARGUMENTS`

---

## Procedure

### Step 1 — Load State

1. Read `.sstack/<feature>/state.md` to get failing spec paths from Phase 4
2. Verify `phase: spec` is marked complete
3. Extract `spec_files:` list and architecture notes from Phase 3

### Step 2 — Implement Each Spec

For each failing spec file:

1. Read the spec file to understand what must pass
2. Identify or create the target source file in `src/**/<feature>.spl`
3. Write the **minimum code** to make specs pass — nothing more
4. Run specs: `bin/simple test <spec_file>`
5. If specs fail, read error output, fix, repeat

### Step 3 — Verify Clean

1. Verify no `pass_todo` stubs remain in implementation files
2. Run full compile check: `bin/simple build check`
3. Update `.sstack/<feature>/state.md` with implementation status

---

## Rules

- **Superpowers TDD:** Spec already exists. Your ONLY job is to make it green.
- **Minimum viable code:** Do not add features beyond what specs require
- **No gold-plating:** No extra methods, no extra error handling, no "nice to have"
- **No refactoring:** Code can be ugly if specs pass. Phase 6 handles cleanup.
- **No stubs:** Every `pass_todo` must be replaced with real implementation
- **Compile clean:** Code must compile without warnings
- **Context budget:** sub-40% — load only the failing spec + target source file

## Boil a Small Lake

Focus on ONE spec file at a time. Make it pass. Move to the next.
Do not read the entire codebase. Do not explore architecture.
Load the spec, load the target file, write code, run test. That is all.

---

## Exit Criteria

- [ ] All spec files from Phase 4 pass: `bin/simple test <spec_file>` green for each
- [ ] No `pass_todo` stubs in implementation files
- [ ] Code compiles cleanly: `bin/simple build check` passes
- [ ] State file updated: `phase: implement` marked complete, `impl_files:` listed

## Output

- Implementation files in `src/**/<feature>.spl`
- Updated `.sstack/<feature>/state.md`
