# CLI unknown-subcommand exit code

> Purpose: Prove that CLI dispatch fall-through exit code.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI unknown-subcommand exit code

Purpose: Prove that CLI dispatch fall-through exit code.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/cli_unknown_subcommand_exit_code_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that CLI dispatch fall-through exit code.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### CLI dispatch fall-through exit code

#### is a usage error (exit 2) for a token that is not an existing file

- is a usage error (exit 2) for a token that is not an existing file
- Verify: is a usage error (exit 2) for a token that is not an existing file
   - Expected: cli_dispatch_fallthrough_exit_code("inspect") equals `2`
   - Expected: cli_dispatch_fallthrough_exit_code("inspect") equals `CLI_USAGE_ERROR_EXIT_CODE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is a usage error (exit 2) for a token that is not an existing file")
step("Verify: is a usage error (exit 2) for a token that is not an existing file")
# @req: REQ-APP-CLI-001
# "inspect" is not a registered subcommand (see the bug doc) and is
# not an existing file in the repo root.
expect(cli_dispatch_fallthrough_exit_code("inspect")).to_equal(2)
expect(cli_dispatch_fallthrough_exit_code("inspect")).to_equal(CLI_USAGE_ERROR_EXIT_CODE)
```

</details>

#### is a usage error for any other misspelled/unimplemented token

- is a usage error for any other misspelled/unimplemented token
- Verify: is a usage error for any other misspelled/unimplemented token
   - Expected: cli_dispatch_fallthrough_exit_code("definitely-not-a-real-subcommand-xyz123") equals `2`
   - Expected: cli_dispatch_fallthrough_exit_code("built") equals `2)  # near-miss of "build"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is a usage error for any other misspelled/unimplemented token")
step("Verify: is a usage error for any other misspelled/unimplemented token")
expect(cli_dispatch_fallthrough_exit_code("definitely-not-a-real-subcommand-xyz123")).to_equal(2)
expect(cli_dispatch_fallthrough_exit_code("built")).to_equal(2)  # near-miss of "build"
```

</details>

#### is NOT the usage-error code when the token resolves to a real file

- is NOT the usage-error code when the token resolves to a real file
- Verify: is NOT the usage-error code when the token resolves to a real file
   - Expected: code equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is NOT the usage-error code when the token resolves to a real file")
step("Verify: is NOT the usage-error code when the token resolves to a real file")
# Non-regression: `bin/simple <real-file>.spl` must keep working —
# this path must not be routed through the exit-2 usage error.
val code = cli_dispatch_fallthrough_exit_code("src/app/main.spl")
expect(code).to_equal(-1)  # oracle: -1 — named expected value from the requirement
assert_not_equal(code, CLI_USAGE_ERROR_EXIT_CODE)
```

</details>

#### CLI_USAGE_ERROR_EXIT_CODE is exit code 2, not 0 or 1

- CLI_USAGE_ERROR_EXIT_CODE is exit code 2, not 0 or 1
- Verify: CLI_USAGE_ERROR_EXIT_CODE is exit code 2, not 0 or 1
   - Expected: CLI_USAGE_ERROR_EXIT_CODE equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CLI_USAGE_ERROR_EXIT_CODE is exit code 2, not 0 or 1")
step("Verify: CLI_USAGE_ERROR_EXIT_CODE is exit code 2, not 0 or 1")
"""
The historical defect was rc=0 (fail-open); a naive fix landing on
rc=1 would collide with "existing file failed to run". Exit 2 keeps
the two cases distinguishable.
"""
expect(CLI_USAGE_ERROR_EXIT_CODE).to_equal(2)  # oracle: 2 — named expected value from the requirement
assert_not_equal(CLI_USAGE_ERROR_EXIT_CODE, 0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-CLI-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `59aba1cf9c80e4ca0f95f5e6ff198bc57d011984ccc6c951fbfbd264ad14b9f2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `59aba1cf9c80e4ca0f95f5e6ff198bc57d011984ccc6c951fbfbd264ad14b9f2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `59aba1cf9c80e4ca0f95f5e6ff198bc57d011984ccc6c951fbfbd264ad14b9f2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/cli/cli_unknown_subcommand_exit_code_spec.spl
mirror: doc/06_spec/01_unit/app/cli/cli_unknown_subcommand_exit_code_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/cli/cli_unknown_subcommand_exit_code_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/cli_unknown_subcommand_exit_code_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/cli_unknown_subcommand_exit_code_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/cli/cli_unknown_subcommand_exit_code_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is a usage error (exit 2) for a token that is not an existing file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/cli_unknown_subcommand_exit_code_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is a usage error for any other misspelled/unimplemented token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/cli_unknown_subcommand_exit_code_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is NOT the usage-error code when the token resolves to a real file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
