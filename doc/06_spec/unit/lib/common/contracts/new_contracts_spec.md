# New Contracts Specification

> Tests covering std.contracts.contracts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# New Contracts Specification

## Scenarios

### std.contracts.contracts

#### simple_contract_check (passing condition)

#### returns silently when condition is 1

- returns silently when condition is 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns silently when condition is 1")
simple_contract_check(1, 0, "test_fn")
expect true == true
```

</details>

#### returns silently when condition is non-zero

- returns silently when condition is non-zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns silently when condition is non-zero")
simple_contract_check(100, 1, "another_fn")
expect true == true
```

</details>

#### accepts kind=2 (error postcondition)

- accepts kind=2 (error postcondition)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts kind=2 (error postcondition)")
simple_contract_check(1, 2, "err_post_fn")
expect true == true
```

</details>

#### accepts empty function name

- accepts empty function name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts empty function name")
simple_contract_check(1, 0, "")
expect true == true
```

</details>

#### accepts kind=5 (assertion)

- accepts kind=5 (assertion)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts kind=5 (assertion)")
simple_contract_check(1, 5, "assert_fn")
expect true == true
```

</details>

#### simple_contract_check_msg (passing condition)

#### returns silently when condition is 1

- returns silently when condition is 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns silently when condition is 1")
simple_contract_check_msg(1, 0, "fn_name", "all good")
expect true == true
```

</details>

#### accepts empty message

- accepts empty message


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts empty message")
simple_contract_check_msg(1, 1, "fn_name", "")
expect true == true
```

</details>

#### accepts empty function name and message

- accepts empty function name and message


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts empty function name and message")
simple_contract_check_msg(1, 3, "", "")
expect true == true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/contracts/new_contracts_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering std.contracts.contracts.
- std.contracts.contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `baede208929d11f9b3695227c35ec3e0fdb322db4a9e9ef4c42c4a5a30470fee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `baede208929d11f9b3695227c35ec3e0fdb322db4a9e9ef4c42c4a5a30470fee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `baede208929d11f9b3695227c35ec3e0fdb322db4a9e9ef4c42c4a5a30470fee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/contracts/new_contracts_spec.spl
mirror: doc/06_spec/unit/lib/common/contracts/new_contracts_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/contracts/new_contracts_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/contracts/new_contracts_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/contracts/new_contracts_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns silently when condition is 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/contracts/new_contracts_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns silently when condition is non-zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/contracts/new_contracts_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts kind=2 (error postcondition)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
