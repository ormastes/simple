# Tuple Match Enum Subpattern Runtime Specification

> Tests covering tuple match with enum sub-patterns selects the right arm.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tuple Match Enum Subpattern Runtime Specification

## Scenarios

### tuple match with enum sub-patterns selects the right arm

#### selects arm 1 only for Red

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects arm 1 only for Red
   - Expected: pick(Color.Red, 5) equals `red-any`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects arm 1 only for Red")
expect(pick(Color.Red, 5)).to_equal("red-any")
```

</details>

#### selects arm 2 for (Green, 0)

- selects arm 2 for (Green, 0)
   - Expected: pick(Color.Green, 0) equals `green-zero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects arm 2 for (Green, 0)")
expect(pick(Color.Green, 0)).to_equal("green-zero")
```

</details>

#### falls through to the default for Blue

- falls through to the default for Blue
   - Expected: pick(Color.Blue, 7) equals `other`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls through to the default for Blue")
expect(pick(Color.Blue, 7)).to_equal("other")
```

</details>

#### handles a nested Option inside the tuple

- handles a nested Option inside the tuple
   - Expected: nested(Some(9), true) equals `some-true-9`
   - Expected: nested(Some(9), false) equals `some-false`
   - Expected: nested(nil, true) equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles a nested Option inside the tuple")
expect(nested(Some(9), true)).to_equal("some-true-9")
expect(nested(Some(9), false)).to_equal("some-false")
expect(nested(nil, true)).to_equal("none")
```

</details>

#### handles an or-pattern inside the tuple

- handles an or-pattern inside the tuple
   - Expected: ored(Color.Red, 1) equals `warm-one`
   - Expected: ored(Color.Blue, 1) equals `warm-one`
   - Expected: ored(Color.Green, 1) equals `rest`
   - Expected: ored(Color.Red, 2) equals `rest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles an or-pattern inside the tuple")
expect(ored(Color.Red, 1)).to_equal("warm-one")
expect(ored(Color.Blue, 1)).to_equal("warm-one")
expect(ored(Color.Green, 1)).to_equal("rest")
expect(ored(Color.Red, 2)).to_equal("rest")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/tuple_match_enum_subpattern_runtime_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering tuple match with enum sub-patterns selects the right arm.
- tuple match with enum sub-patterns selects the right arm

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `8d002d8f2052363308e08a4a4ee33f21dbd4cf81773423d90c827083894de32a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8d002d8f2052363308e08a4a4ee33f21dbd4cf81773423d90c827083894de32a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8d002d8f2052363308e08a4a4ee33f21dbd4cf81773423d90c827083894de32a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/hir/tuple_match_enum_subpattern_runtime_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/tuple_match_enum_subpattern_runtime_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/tuple_match_enum_subpattern_runtime_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/tuple_match_enum_subpattern_runtime_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/tuple_match_enum_subpattern_runtime_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects arm 1 only for Red' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/tuple_match_enum_subpattern_runtime_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects arm 2 for (Green, 0)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/tuple_match_enum_subpattern_runtime_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls through to the default for Blue' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
