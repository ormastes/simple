# SPipe Phase 7: Verify -- QA

**Role:** QA -- Full validation: tests, coverage, docs, production readiness
**Blinders:** ONLY verification. No code changes except critical fixes.
**Context budget:** sub-40% -- load only test output + coverage reports.

## State

- **Read:** `.spipe/<feature>/state.md` -- get all file paths from Phases 4-6
- **Write:** `.spipe/<feature>/state.md` -- update with verification report

## Entry Criteria

- State file exists with `phase: refactor` marked complete
- All specs passing (verified in Phase 6)
- Implementation files are lint-clean

## Process

1. Read `.spipe/<feature>/state.md` to get all file paths
2. Verify `bin/simple` exists before running any command. If it is missing,
   write a setup-failure report to the state file and exit immediately; do not
   retry or enter a test-fix loop.
3. Run feature specs first: `set -o pipefail; bin/simple test <spec_file> 2>&1 | tail -40` for each spec from Phase 4
4. Run full test suite with capped output: `set -o pipefail; bin/simple test 2>&1 | tail -60` (pipefail preserves test exit code; check last lines for pass/fail summary)
5. Run build checks: `set -o pipefail; bin/simple build check 2>&1 | tail -30`
6. Run numbered artifact guard:
   `sh scripts/audit/numbered-artifact-guard.shs --working`
   `sh scripts/audit/numbered-artifact-guard.shs --staged`
7. Run workspace root guard: `sh scripts/check-workspace-root-guard.shs audit --strict`
   If WRG001/WRG002/WRG003 violations appear:
   - Trace which implementation step, spec, or tool created the violating file
   - Fix the root cause (wrong path in code, wrong directory target, misplaced test)
   - Do NOT quarantine or suppress as a workaround
   - If the file is intentional, add it to the appropriate FILE.md manifest
   - Re-run the guard to confirm clean
8. Run doc coverage: `set -o pipefail; bin/simple doc-coverage 2>&1 | tail -30`
9. Check for remaining stubs:
   - Search impl files for `pass_todo` -- must be zero
   - Search impl files for `pass_do_nothing` -- must be intentional
9. Verify documentation exists for public API surfaces
10. Verify generated scenario manual quality for scenario-oriented specs:
   - mirrored `doc/06_spec/...` exists
   - primary scenario flow is visible as manual steps
   - inline/previous setup is expanded without redundant `Previous:` text
   - executable SPipe is folded by default
   - advanced/edge/matrix/stress/helper-only scenarios are folded or skipped by policy
   - captures are attached to relevant steps and use meaningful kinds for UI,
     API, protocol, execution, binary, text, log, or artifact evidence
11. Compile verification report:
   - Test results (pass/fail counts)
   - Coverage percentage (target: 80%+)
   - Doc coverage for new code
   - Scenario manual quality result for generated docs
   - Any remaining issues
12. If critical issues found (max 3 fix-recheck cycles; escalate after 3):
   a. Fix ONLY test/doc issues (not feature code)
   b. Re-run affected checks with `set -o pipefail; ... 2>&1 | tail -40` output cap
13. Update state file with verification report

## Rules

- **Do not change feature behavior:** Only fix tests, docs, or trivial issues
- **80% coverage target:** Flag if new code is below threshold
- **No pass_todo allowed:** Every stub must be implemented or removed
- **Full suite must pass:** Not just feature specs -- the entire test suite
- **Document public APIs:** Every public function needs doc comments
- **Generated scenario manuals:** Scenario-oriented specs must produce
  hand-written-quality manual output, not raw test dumps
- **Critical fix only:** If implementation has a bug, send back to Phase 5
- **No numbered artifacts:** New or renamed files with copy/version names like
  `foo_1`, `foo_2`, `part1`, `ver1`, or `v1` fail verification
- **No duplication:** Check line-level, token-level, and semantic duplicates;
  parameter lists with 3+ fields should be a struct
- **Cohesion:** Each file covers one concern; flag files over 300 lines for split
- **Minimal public interface:** Minimize exports per layer and per feature
- **TLDR docs:** Every new architecture/design doc must have a `_tldr.md` companion
  (≤30 lines with diagram)

## Boil a Small Lake

Run ONE check at a time. Record the result. Move to the next check.
Do not try to fix everything at once. Verify, report, then fix in order.
If a fix requires significant code changes, flag it for Phase 5 re-entry.

## Exit Criteria

- [ ] Full test suite green: `bin/simple test` passes
- [ ] Build checks pass: `bin/simple build check` clean
- [ ] Coverage at 80%+ for new code
- [ ] Doc coverage exists for public APIs
- [ ] Scenario-oriented generated docs pass manual quality review
- [ ] No `pass_todo` stubs remain
- [ ] Numbered artifact guard passes
- [ ] Workspace root guard passes: `sh scripts/check-workspace-root-guard.shs audit --strict` clean
- [ ] Verification report written in state file
- [ ] State file updated: `phase: verify` marked complete

## Output

- Verification report in `.spipe/<feature>/state.md`
- Any minor fixes applied (test/doc only)
