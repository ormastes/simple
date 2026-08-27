# CMM Parser V4 Fixes Specification

> Executes the real CMM V4 parser-fix harness (examples/10_tooling/trace32_tools/cmm_lsp/test_v4_fixes.spl), which parses each fixed real-world pattern through parse_cmm_source and reports Passed/Failed/Total. The examples tree cannot be imported from specs (its numeric path segment 10_tooling is unparseable in a use path), so the spec runs the harness as the production entry point and asserts its verdict.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CMM Parser V4 Fixes Specification

Executes the real CMM V4 parser-fix harness (examples/10_tooling/trace32_tools/cmm_lsp/test_v4_fixes.spl), which parses each fixed real-world pattern through parse_cmm_source and reports Passed/Failed/Total. The examples tree cannot be imported from specs (its numeric path segment 10_tooling is unparseable in a use path), so the spec runs the harness as the production entry point and asserts its verdict.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CMM-PARSE-V4 |
| Category | Tooling |
| Status | Implemented |
| Source | `test/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Executes the real CMM V4 parser-fix harness
(examples/10_tooling/trace32_tools/cmm_lsp/test_v4_fixes.spl), which parses
each fixed real-world pattern through parse_cmm_source and reports
Passed/Failed/Total. The examples tree cannot be imported from specs (its
numeric path segment 10_tooling is unparseable in a use path), so the spec
runs the harness as the production entry point and asserts its verdict.

## Scenarios

### CMM Parser V4 - line continuation, C++ scope, IF/ELSE blocks

#### every fixed real-world CMM pattern parses without errors

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Verify: harness summary reports zero failed patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: harness summary reports zero failed patterns")
val (stdout, code) = run_v4_fixes_harness()
expect(stdout).to_contain("=== V4 Fixes Test Results ===")
expect(stdout).to_contain("Failed: 0")  # oracle: no fixed pattern may regress
```

</details>

#### harness executes to completion over all documented patterns

- Verify: harness ran every pattern and printed a total
   - Expected: stdout does not contain `Passed: 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: harness ran every pattern and printed a total")
val (stdout, _code) = run_v4_fixes_harness()
expect(stdout).to_contain("Total: ")  # oracle: summary total is present
expect(stdout.contains("Passed: 0")).to_equal(false)  # oracle: not a vacuous run
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8ae553f3fb6c0230881cd41b39490f5b4451c42b98f78b4a8e220b2bb536b41c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8ae553f3fb6c0230881cd41b39490f5b4451c42b98f78b4a8e220b2bb536b41c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8ae553f3fb6c0230881cd41b39490f5b4451c42b98f78b4a8e220b2bb536b41c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.spl
mirror: doc/06_spec/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'every fixed real-world CMM pattern parses without errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'harness executes to completion over all documented patterns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
