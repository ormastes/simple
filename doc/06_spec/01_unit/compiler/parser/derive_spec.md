# Derive Specification

> Tests covering @derive annotation parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Derive Specification

## Scenarios

### @derive annotation parsing

#### struct with @derive comment can be constructed

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- struct with @derive comment can be constructed
   - Expected: c.r equals `255`
   - Expected: c.g equals `128`
   - Expected: c.b equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("struct with @derive comment can be constructed")
val c = Color(r: 255, g: 128, b: 0)
expect(c.r).to_equal(255)
expect(c.g).to_equal(128)
expect(c.b).to_equal(0)
```

</details>

#### another derived struct works

- another derived struct works
   - Expected: p.x equals `3`
   - Expected: p.y equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("another derived struct works")
val p = Point2D(x: 3, y: 4)
expect(p.x).to_equal(3)
expect(p.y).to_equal(4)
```

</details>

#### derived struct fields are accessible

- derived struct fields are accessible
   - Expected: sum equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("derived struct fields are accessible")
val c = Color(r: 0, g: 255, b: 0)
val sum = c.r + c.g + c.b
expect(sum).to_equal(255)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/derive_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering @derive annotation parsing.
- @derive annotation parsing

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `059deb2823c797100642e7649f9e6364250ac3d7bad66cb2b2f15815e2e9f28b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `059deb2823c797100642e7649f9e6364250ac3d7bad66cb2b2f15815e2e9f28b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `059deb2823c797100642e7649f9e6364250ac3d7bad66cb2b2f15815e2e9f28b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/parser/derive_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/derive_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/derive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/derive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/derive_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/parser/derive_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'struct with @derive comment can be constructed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/derive_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'another derived struct works' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/derive_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derived struct fields are accessible' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
