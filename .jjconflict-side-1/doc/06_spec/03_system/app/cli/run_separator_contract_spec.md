# Run Separator Contract Specification

> Tests covering simple run separator.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Run Separator Contract Specification

## Scenarios

### simple run separator

#### consumes evidence before -- and passes post-separator tokens literally

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- consumes evidence before -- and passes post-separator tokens literally
   - Expected: before_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("consumes evidence before -- and passes post-separator tokens literally")
val (before_out, _before_err, before_code) = run_probe(["--test-result-file=before.json", "--", "--test-result-file=after.json"])
expect(before_code).to_equal(0)
expect(before_out).to_contain("evidence=before.json")
expect(before_out).to_contain("args=--|--test-result-file=after.json")
```

</details>

#### does not treat post-separator evidence as an internal option

- does not treat post-separator evidence as an internal option
   - Expected: after_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not treat post-separator evidence as an internal option")
val inherited = env_get("SIMPLE_TEST_RESULT_FILE") ?? ""
val (after_out, _after_err, after_code) = run_probe(["--", "--test-result-file=after.json"])
expect(after_code).to_equal(0)
expect(after_out).to_contain("evidence=" + inherited + "\n")
expect(after_out).to_contain("args=--|--test-result-file=after.json")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/cli/run_separator_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering simple run separator.
- simple run separator

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

- Canonical SPipe generation for source `94bf3e1ca0c7716f97926c5d810bb81fe1d93b197fd2e48cb70b29277fe4b54e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `94bf3e1ca0c7716f97926c5d810bb81fe1d93b197fd2e48cb70b29277fe4b54e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `94bf3e1ca0c7716f97926c5d810bb81fe1d93b197fd2e48cb70b29277fe4b54e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/cli/run_separator_contract_spec.spl
mirror: doc/06_spec/03_system/app/cli/run_separator_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/cli/run_separator_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/cli/run_separator_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/cli/run_separator_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/cli/run_separator_contract_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'consumes evidence before -- and passes post-separator tokens literally' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/cli/run_separator_contract_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not treat post-separator evidence as an internal option' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
