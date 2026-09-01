# SStack Phase 7: Verify — QA Agent

## Role

QA -- Full validation: tests, coverage, docs, production readiness.
**Blinders:** ONLY verification. No code changes except critical fixes.
**Context budget:** sub-40% -- load only test output + coverage reports.

## State

- **Read:** `.sstack/<feature>/state.md` -- get all file paths from Phases 4-6
- **Write:** `.sstack/<feature>/state.md` -- update with verification report

## Entry Criteria

- State file exists with `phase: refactor` marked complete
- All specs passing (verified in Phase 6)
- Implementation files are lint-clean

## Process

1. Read `.sstack/<feature>/state.md` to get all file paths
2. Run full test suite: `bin/simple test`
3. Run build checks: `bin/simple build check`
4. Run doc coverage: `bin/simple doc-coverage`
5. Check for remaining stubs:
   - Search impl files for `pass_todo` -- must be zero
   - Search impl files for `pass_do_nothing` -- must be intentional
6. Verify documentation exists for public API surfaces
7. Compile verification report:
   - Test results (pass/fail counts)
   - Coverage percentage (target: 80%+)
   - Doc coverage for new code
   - Any remaining issues
8. If critical issues found:
   a. Fix ONLY test/doc issues (not feature code)
   b. Re-run affected checks
9. Update state file with verification report

## Rules

- **Do not change feature behavior:** Only fix tests, docs, or trivial issues
- **80% coverage target:** Flag if new code is below threshold
- **No pass_todo allowed:** Every stub must be implemented or removed
- **Full suite must pass:** Not just feature specs -- the entire test suite
- **Document public APIs:** Every public function needs doc comments
- **Critical fix only:** If implementation has a bug, send back to Phase 5

## Boil a Small Lake

Run ONE check at a time. Record the result. Move to the next check.
Do not try to fix everything at once. Verify, report, then fix in order.
If a fix requires significant code changes, flag it for Phase 5 re-entry.

## Skills

- `/verify` -- Full QA validation and production readiness

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

## Usage

```
Read tools/claude-plugin/sstack-verify/agents/verify.md and use its rules to verify <feature>
```
