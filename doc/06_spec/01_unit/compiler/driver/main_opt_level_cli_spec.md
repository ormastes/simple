# Main Opt Level Cli Specification

> Tests covering the standalone driver subprocess actually ran, standalone driver opt-level parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Main Opt Level Cli Specification

## Scenarios

### the standalone driver subprocess actually ran

#### produces driver output rather than failing silently

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces driver output rather than failing silently
   - Expected: result.0 == "" is false
   - Expected: result.0 does not contain `refusing non-production`
   - Expected: result.2 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("produces driver output rather than failing silently")
val result = run_standalone_driver("simple-compiler --opt-level=4 missing_input.spl")
expect(result.0 == "").to_equal(false)
expect(result.0.contains("refusing non-production")).to_equal(false)
# the driver's own verdict, not a wrapper refusal
expect(result.2).to_equal(1)
expect(result.0).to_contain("Optimization level must be 0-3")
```

</details>

### standalone driver opt-level parsing

#### accepts inline legacy numeric opt levels 0 through 3

- accepts inline legacy numeric opt levels 0 through 3
   - Expected: result.0 does not contain `Invalid optimization level`
   - Expected: result.0 does not contain `Optimization level must be 0-3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts inline legacy numeric opt levels 0 through 3")
val levels = ["0", "1", "2", "3"]
for level in levels:
    val result = run_standalone_driver("simple-compiler --opt-level=" + level + " missing_input.spl")
    expect(result.0.contains("Invalid optimization level")).to_equal(false)
    expect(result.0.contains("Optimization level must be 0-3")).to_equal(false)
```

</details>

#### accepts split legacy numeric opt levels 0 through 3

- accepts split legacy numeric opt levels 0 through 3
   - Expected: result.0 does not contain `Invalid optimization level`
   - Expected: result.0 does not contain `Optimization level must be 0-3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts split legacy numeric opt levels 0 through 3")
val levels = ["0", "1", "2", "3"]
for level in levels:
    val result = run_standalone_driver("simple-compiler --opt-level " + level + " missing_input.spl")
    expect(result.0.contains("Invalid optimization level")).to_equal(false)
    expect(result.0.contains("Optimization level must be 0-3")).to_equal(false)
```

</details>

#### rejects non-numeric legacy opt levels

- rejects non-numeric legacy opt levels
   - Expected: result.2 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects non-numeric legacy opt levels")
val result = run_standalone_driver("simple-compiler --opt-level=basic missing_input.spl")
expect(result.2).to_equal(1)
expect(result.0).to_contain("Invalid optimization level: basic")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/main_opt_level_cli_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering the standalone driver subprocess actually ran, standalone driver opt-level parsing.
- the standalone driver subprocess actually ran
- standalone driver opt-level parsing

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5110c21f548eeef7eb0c426113dea1e731037008ad703ea0f3e54fd3a289f5e7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5110c21f548eeef7eb0c426113dea1e731037008ad703ea0f3e54fd3a289f5e7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5110c21f548eeef7eb0c426113dea1e731037008ad703ea0f3e54fd3a289f5e7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/driver/main_opt_level_cli_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/main_opt_level_cli_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/main_opt_level_cli_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/main_opt_level_cli_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/main_opt_level_cli_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/main_opt_level_cli_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces driver output rather than failing silently' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/main_opt_level_cli_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts inline legacy numeric opt levels 0 through 3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/main_opt_level_cli_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts split legacy numeric opt levels 0 through 3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
