# borrowing_spec

> Reference Capabilities and Borrowing Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# borrowing_spec

Reference Capabilities and Borrowing Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Memory Management |
| Status | In Progress |
| Source | `test/03_system/feature/usage/borrowing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Reference Capabilities and Borrowing Specification

Tests for the borrowing system including mutable (mut T), isolated (iso T),
and immutable reference capabilities. Verifies proper ownership transfer,
mutable access restrictions, and isolation guarantees.

## Scenarios

### Borrowing and Reference Capabilities

#### Immutable references

#### allows multiple immutable borrows

- allows multiple immutable borrows


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows multiple immutable borrows")
skip
```

</details>

#### Mutable references

#### prevents simultaneous immutable and mutable borrows

- prevents simultaneous immutable and mutable borrows


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prevents simultaneous immutable and mutable borrows")
skip
```

</details>

#### Isolated references

#### ensures exclusive access to isolated values

- ensures exclusive access to isolated values


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ensures exclusive access to isolated values")
skip
```

</details>

#### Ownership transfer

#### transfers ownership correctly through function calls

- transfers ownership correctly through function calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("transfers ownership correctly through function calls")
skip
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1a9615307a2cdaa6591030f23b81e72846da89898f7c9b3e0667fc3ee52c3ca4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1a9615307a2cdaa6591030f23b81e72846da89898f7c9b3e0667fc3ee52c3ca4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1a9615307a2cdaa6591030f23b81e72846da89898f7c9b3e0667fc3ee52c3ca4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/feature/usage/borrowing_spec.spl
mirror: doc/06_spec/03_system/feature/usage/borrowing_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/feature/usage/borrowing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/borrowing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/borrowing_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/feature/usage/borrowing_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows multiple immutable borrows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/borrowing_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prevents simultaneous immutable and mutable borrows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/borrowing_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ensures exclusive access to isolated values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
