# SStack Phase 7: Verify Skill — QA

**Self-sufficient.** Any LLM (Claude, Codex, Gemini) can run this phase independently. Does not depend on any other LLM having participated in prior steps.

Full validation: tests, coverage, docs, production readiness. No code changes except critical fixes.

## Usage

```
/verify                              # Verify from state file
/verify path/to/feature              # Verify specific feature
```

Argument: `$ARGUMENTS`

---

## Procedure

### Step 1 — Load State

1. Read `.sstack/<feature>/state.md` to get all file paths from Phases 4-6
2. Verify `phase: refactor` is marked complete
3. Extract all spec, impl, and doc file paths

### Step 2 — Run Full Test Suite

1. Run full test suite: `bin/simple test`
2. Run build checks: `bin/simple build check`
3. Record pass/fail counts

### Step 3 — Check Coverage and Stubs

1. Run doc coverage: `bin/simple doc-coverage`
2. Search impl files for `pass_todo` — must be zero
3. Search impl files for `pass_do_nothing` — must be intentional
4. Verify documentation exists for public API surfaces

### Step 4 — Compile Verification Report

Compile results into:
- Test results (pass/fail counts)
- Coverage percentage (target: 80%+)
- Doc coverage for new code
- Any remaining issues

### Step 5 — Handle Critical Issues

If critical issues found:
1. Fix ONLY test/doc issues (not feature code)
2. Re-run affected checks
3. If implementation has a bug, flag for Phase 5 re-entry

### Step 6 — Update State

Update `.sstack/<feature>/state.md` with verification report.

---

## Rules

- **Do not change feature behavior:** Only fix tests, docs, or trivial issues
- **80% coverage target:** Flag if new code is below threshold
- **No pass_todo allowed:** Every stub must be implemented or removed
- **Full suite must pass:** Not just feature specs — the entire test suite
- **Document public APIs:** Every public function needs doc comments
- **Critical fix only:** If implementation has a bug, send back to Phase 5
- **Context budget:** sub-40% — load only test output + coverage reports

## Boil a Small Lake

Run ONE check at a time. Record the result. Move to the next check.
Do not try to fix everything at once. Verify, report, then fix in order.
If a fix requires significant code changes, flag it for Phase 5 re-entry.

---

## Exit Criteria

- [ ] Full test suite green: `bin/simple test` passes
- [ ] Build checks pass: `bin/simple build check` clean
- [ ] Coverage at 80%+ for new code
- [ ] Doc coverage exists for public APIs
- [ ] No `pass_todo` stubs remain
- [ ] Verification report written in state file
- [ ] State file updated: `phase: verify` marked complete

## Output

- Verification report in `.sstack/<feature>/state.md`
- Any minor fixes applied (test/doc only)
