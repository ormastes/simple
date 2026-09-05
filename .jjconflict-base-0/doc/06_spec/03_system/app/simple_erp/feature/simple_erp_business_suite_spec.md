# Simple Erp Business Suite Specification

> Tests covering simple erp business suite.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Erp Business Suite Specification

## Scenarios

### simple erp business suite

#### runs every lane through the shared guarded-write framework

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs every lane through the shared guarded-write framework
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs every lane through the shared guarded-write framework")
val result = shell("bin/release/x86_64-unknown-linux-gnu/simple examples/12_business/simple_erp/src/business_suite.spl")
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_contain("Business Suite:")
expect(result.stdout).to_contain("lane=crm status=ok accepted=1 denied=1")
expect(result.stdout).to_contain("lane=reservation status=ok accepted=1 denied=1")
expect(result.stdout).to_contain("lane=sale status=ok accepted=1 denied=1")
expect(result.stdout).to_contain("lane=market status=ok accepted=1 denied=1")
expect(result.stdout).to_contain("lane=restaurant status=ok accepted=1 denied=1")
```

</details>

#### exposes the web route table and framework gate evidence

- exposes the web route table and framework gate evidence
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes the web route table and framework gate evidence")
val result = shell("bin/release/x86_64-unknown-linux-gnu/simple examples/12_business/simple_erp/src/business_suite.spl")
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_contain("routes=7")
expect(result.stdout).to_contain("ledger_balanced=true")
expect(result.stdout).to_contain("approval=enforced")
expect(result.stdout).to_contain("denied=needs-approval")
expect(result.stdout).to_contain("framework=guarded-write gates=session+rbac+validation+idempotency")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_erp/feature/simple_erp_business_suite_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering simple erp business suite.
- simple erp business suite

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `664d648e748cfe81e6b1cd453c4fdab37b6ecebea4499cad9bd32a52d2a5629f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `664d648e748cfe81e6b1cd453c4fdab37b6ecebea4499cad9bd32a52d2a5629f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `664d648e748cfe81e6b1cd453c4fdab37b6ecebea4499cad9bd32a52d2a5629f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/simple_erp/feature/simple_erp_business_suite_spec.spl
mirror: doc/06_spec/03_system/app/simple_erp/feature/simple_erp_business_suite_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simple_erp/feature/simple_erp_business_suite_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_erp/feature/simple_erp_business_suite_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_erp/feature/simple_erp_business_suite_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simple_erp/feature/simple_erp_business_suite_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs every lane through the shared guarded-write framework' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_erp/feature/simple_erp_business_suite_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes the web route table and framework gate evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
