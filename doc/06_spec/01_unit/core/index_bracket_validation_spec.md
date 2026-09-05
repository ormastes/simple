# Index Bracket Validation Specification

> Tests covering core bracket expression validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Index Bracket Validation Specification

## Scenarios

### core bracket expression validation

#### rejects comparison in index position

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects comparison in index position
   - Expected: parse_fails("fn main() -> i64:\n    val s = \"abc\"\n    return s[1 == 0]") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects comparison in index position")
expect(parse_fails("fn main() -> i64:\n    val s = \"abc\"\n    return s[1 == 0]")).to_equal(true)
```

</details>

#### rejects logical and in index position

- rejects logical and in index position
   - Expected: parse_fails("fn main() -> i64:\n    val arr = [1, 2, 3]\n    return arr[true and false]") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects logical and in index position")
expect(parse_fails("fn main() -> i64:\n    val arr = [1, 2, 3]\n    return arr[true and false]")).to_equal(true)
```

</details>

#### rejects logical not in index position

- rejects logical not in index position
   - Expected: parse_fails("fn main() -> i64:\n    val arr = [1, 2, 3]\n    return arr[not false]") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects logical not in index position")
expect(parse_fails("fn main() -> i64:\n    val arr = [1, 2, 3]\n    return arr[not false]")).to_equal(true)
```

</details>

#### rejects comparison slice start

- rejects comparison slice start
   - Expected: parse_fails("fn main() -> i64:\n    val s = \"abc\"\n    return len(s[1 < 2:2])") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects comparison slice start")
expect(parse_fails("fn main() -> i64:\n    val s = \"abc\"\n    return len(s[1 < 2:2])")).to_equal(true)
```

</details>

#### rejects comparison slice end

- rejects comparison slice end
   - Expected: parse_fails("fn main() -> i64:\n    val s = \"abc\"\n    return len(s[0:1 == 1])") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects comparison slice end")
expect(parse_fails("fn main() -> i64:\n    val s = \"abc\"\n    return len(s[0:1 == 1])")).to_equal(true)
```

</details>

#### still allows arithmetic indexes

- still allows arithmetic indexes
   - Expected: parse_fails("fn main() -> i64:\n    val arr = [1, 2, 3]\n    return arr[1 + 1]") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still allows arithmetic indexes")
expect(parse_fails("fn main() -> i64:\n    val arr = [1, 2, 3]\n    return arr[1 + 1]")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/core/index_bracket_validation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering core bracket expression validation.
- core bracket expression validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `37b672c69f86e29b2ebde0b5969541b4510ad5e2a06f7491e0bb06f591a360c7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `37b672c69f86e29b2ebde0b5969541b4510ad5e2a06f7491e0bb06f591a360c7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `37b672c69f86e29b2ebde0b5969541b4510ad5e2a06f7491e0bb06f591a360c7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/core/index_bracket_validation_spec.spl
mirror: doc/06_spec/01_unit/core/index_bracket_validation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/core/index_bracket_validation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/core/index_bracket_validation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/core/index_bracket_validation_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects comparison in index position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/core/index_bracket_validation_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects logical and in index position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/core/index_bracket_validation_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects logical not in index position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
