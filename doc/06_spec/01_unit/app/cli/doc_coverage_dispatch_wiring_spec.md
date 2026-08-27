# Doc Coverage Dispatch Wiring Specification

> Tests covering doc-coverage CLI dispatch wiring.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Doc Coverage Dispatch Wiring Specification

## Scenarios

### doc-coverage CLI dispatch wiring

#### the doc-coverage app is a runnable script, not a bare library module

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- the doc-coverage app is a runnable script, not a bare library module
   - Expected: source.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the doc-coverage app is a runnable script, not a bare library module")
val source = app_source()
expect(source.len() > 0).to_equal(true)
expect(source).to_contain("fn handle_doc_coverage_command(args: [text]) -> i64:")
# The defect: no top-level entry point at all.
expect(source).to_contain("fn main() -> i64:")
expect(source).to_contain("handle_doc_coverage_command(cmd_args)")
expect(source).to_contain("cli_get_args")
```

</details>

#### the driver's dispatch allowlist names the doc-coverage app_path

- the driver's dispatch allowlist names the doc-coverage app_path
   - Expected: source.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the driver's dispatch allowlist names the doc-coverage app_path")
val source = driver_source()
expect(source.len() > 0).to_equal(true)
# The CommandEntry has always pointed here...
expect(source).to_contain("app_path: \"src/app/cli/doc_coverage_command.spl\"")
# ...but dispatch_to_simple_app must also admit it, or it returns None.
expect(source).to_contain("app_relative_path != \"src/app/cli/doc_coverage_command.spl\"")
```

</details>

#### the same-family pure-Simple tools stats/coverage/dap are admitted too

- the same-family pure-Simple tools stats/coverage/dap are admitted too


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the same-family pure-Simple tools stats/coverage/dap are admitted too")
val source = driver_source()
expect(source).to_contain("app_relative_path != \"src/app/cli/stats_entry.spl\"")
expect(source).to_contain("app_relative_path != \"src/app/coverage/main.spl\"")
expect(source).to_contain("app_relative_path != \"src/app/dap/main.spl\"")
```

</details>

#### refusing the Rust fallback is still fail-closed, never a silent success

- refusing the Rust fallback is still fail-closed, never a silent success


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refusing the Rust fallback is still fail-closed, never a silent success")
val source = driver_source()
expect(source).to_contain("refusing Rust fallback")
expect(source).to_contain("if pure_simple_tool {")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/doc_coverage_dispatch_wiring_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering doc-coverage CLI dispatch wiring.
- doc-coverage CLI dispatch wiring

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c2cbe7019e4a49b4ff20d261bf96e9fbd81f458ac8d4edd1264e12fb35ee959c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c2cbe7019e4a49b4ff20d261bf96e9fbd81f458ac8d4edd1264e12fb35ee959c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c2cbe7019e4a49b4ff20d261bf96e9fbd81f458ac8d4edd1264e12fb35ee959c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/cli/doc_coverage_dispatch_wiring_spec.spl
mirror: doc/06_spec/01_unit/app/cli/doc_coverage_dispatch_wiring_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/cli/doc_coverage_dispatch_wiring_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/doc_coverage_dispatch_wiring_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/doc_coverage_dispatch_wiring_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the doc-coverage app is a runnable script, not a bare library module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/doc_coverage_dispatch_wiring_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the driver's dispatch allowlist names the doc-coverage app_path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/doc_coverage_dispatch_wiring_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the same-family pure-Simple tools stats/coverage/dap are admitted too' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
