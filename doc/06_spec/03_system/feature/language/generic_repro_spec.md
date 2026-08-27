# Generic Repro Specification

> Tests covering generic syntax repros.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic Repro Specification

## Scenarios

### generic syntax repros

#### dispatches methods through a generic type alias

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- dispatches methods through a generic type alias
   - Expected: values.length() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dispatches methods through a generic type alias")
val values = ReproIntVec(items: [])
values.push(10)
expect(values.length()).to_equal(1)
```

</details>

#### parses generic instance method calls

- parses generic instance method calls
   - Expected: box.get() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses generic instance method calls")
val box = ReproBox<i64>(value: 42)
expect(box.get()).to_equal(42)
```

</details>

#### parses explicit generic function calls

- parses explicit generic function calls
   - Expected: repro_identity<i64>(42) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses explicit generic function calls")
expect(repro_identity<i64>(42)).to_equal(42)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/language/generic_repro_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering generic syntax repros.
- generic syntax repros

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `db681e887a22f3319b2db73aefedfac4ce7f48f9ff1276981d0e9903a489e446`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db681e887a22f3319b2db73aefedfac4ce7f48f9ff1276981d0e9903a489e446`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db681e887a22f3319b2db73aefedfac4ce7f48f9ff1276981d0e9903a489e446`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/language/generic_repro_spec.spl
mirror: doc/06_spec/03_system/feature/language/generic_repro_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/language/generic_repro_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/language/generic_repro_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/language/generic_repro_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/language/generic_repro_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches methods through a generic type alias' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/language/generic_repro_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses generic instance method calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/language/generic_repro_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses explicit generic function calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
