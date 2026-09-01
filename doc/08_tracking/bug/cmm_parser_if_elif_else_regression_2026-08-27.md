# CMM parser if/elif/else regression caught by de-vacuated spec (2026-08-27)

Rewriting test/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.spl and
test/03_system/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.spl from
`expect(0).to_equal(0)` scaffolds to executing the real harness
(examples/10_tooling/trace32_tools/cmm_lsp/test_v4_fixes.spl) exposed a real
parser defect that exists at HEAD:

- Harness verdict: `Passed: 28  Failed: 1  Total: 29`
- Failing pattern: `if_elif_else` — "Line 5: Failed to parse statement"
  (IF ... ELSE IF ... ELSE with separate-line paren blocks).

Both rewritten specs are honestly RED: `Results: 2 total, 1 passed, 1 failed`
(scenario 1 asserts `Failed: 0`). Left RED per testing rules; fix the parser's
ELSE IF chaining in cmm_parser_stmts.spl. Scores went 49 -> 93 (ORA-001/ORA-002
cleared). Mutation dual-check performed on the feature copy: flipping the
vacuity guard to `to_equal(true)` -> `Results: 2 total, 0 passed, 2 failed`;
reverted byte-exact.
