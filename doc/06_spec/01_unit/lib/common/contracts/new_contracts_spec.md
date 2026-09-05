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
   - Expected: "test_fn" equals `test_fn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns silently when condition is 1")
simple_contract_check(1, 0, "test_fn")
expect("test_fn").to_equal("test_fn")
```

</details>

#### returns silently when condition is non-zero

- returns silently when condition is non-zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns silently when condition is non-zero")
simple_contract_check(100, 1, "another_fn")
expect(100).to_be_greater_than(1)
```

</details>

#### accepts kind=2 (error postcondition)

- accepts kind=2 (error postcondition)
   - Expected: 2 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts kind=2 (error postcondition)")
simple_contract_check(1, 2, "err_post_fn")
expect(2).to_equal(2)
```

</details>

#### accepts empty function name

- accepts empty function name
   - Expected: "" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts empty function name")
simple_contract_check(1, 0, "")
expect("").to_equal("")
```

</details>

#### accepts kind=5 (assertion)

- accepts kind=5 (assertion)
   - Expected: 5 equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts kind=5 (assertion)")
simple_contract_check(1, 5, "assert_fn")
expect(5).to_equal(5)
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
# @req REQ-SSPEC-LIB
step("returns silently when condition is 1")
simple_contract_check_msg(1, 0, "fn_name", "all good")
expect("all good").to_contain("good")
```

</details>

#### accepts empty message

- accepts empty message
   - Expected: "" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts empty message")
simple_contract_check_msg(1, 1, "fn_name", "")
expect("").to_equal("")
```

</details>

#### accepts empty function name and message

- accepts empty function name and message
   - Expected: 3 equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts empty function name and message")
simple_contract_check_msg(1, 3, "", "")
expect(3).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/contracts/new_contracts_spec.spl` |
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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1c7abca74c9690c28d1b6a057a748dcf38c65e89e9bb2d17be111a6fa2cb9017`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1c7abca74c9690c28d1b6a057a748dcf38c65e89e9bb2d17be111a6fa2cb9017`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1c7abca74c9690c28d1b6a057a748dcf38c65e89e9bb2d17be111a6fa2cb9017`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/contracts/new_contracts_spec.spl
mirror: doc/06_spec/01_unit/lib/common/contracts/new_contracts_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/contracts/new_contracts_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/contracts/new_contracts_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/contracts/new_contracts_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/contracts/new_contracts_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns silently when condition is 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/contracts/new_contracts_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns silently when condition is non-zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/contracts/new_contracts_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts kind=2 (error postcondition)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
