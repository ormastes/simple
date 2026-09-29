# Typed Empty Array Constructor Specification

> Tests covering typed empty array constructor [i64]().

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Typed Empty Array Constructor Specification

## Scenarios

### typed empty array constructor [i64]()

#### constructs an empty i64 array

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- constructs an empty i64 array
   - Expected: allowed.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("constructs an empty i64 array")
val allowed: [i64] = [i64]()
expect(allowed.len()).to_equal(0)
```

</details>

#### constructed array accepts pushes

- constructed array accepts pushes
   - Expected: xs.len() equals `2`
   - Expected: xs[0] + xs[1] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("constructed array accepts pushes")
var xs: [i64] = [i64]()
xs.push(41)
xs.push(1)
expect(xs.len()).to_equal(2)
expect(xs[0] + xs[1]).to_equal(42)
```

</details>

#### matches the [] spelling

- matches the [] spelling
   - Expected: a.len() equals `b.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matches the [] spelling")
val a: [i64] = [i64]()
val b: [i64] = []
expect(a.len()).to_equal(b.len())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantic/typed_empty_array_constructor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering typed empty array constructor [i64]().
- typed empty array constructor [i64]()

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

- Canonical SPipe generation for source `f3cc065bd6977c251b1db9b1f5f2dbae59c006b648d3114796b79fce1e7cc8b5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f3cc065bd6977c251b1db9b1f5f2dbae59c006b648d3114796b79fce1e7cc8b5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f3cc065bd6977c251b1db9b1f5f2dbae59c006b648d3114796b79fce1e7cc8b5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/semantic/typed_empty_array_constructor_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantic/typed_empty_array_constructor_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantic/typed_empty_array_constructor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantic/typed_empty_array_constructor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantic/typed_empty_array_constructor_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/semantic/typed_empty_array_constructor_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs an empty i64 array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantic/typed_empty_array_constructor_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructed array accepts pushes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantic/typed_empty_array_constructor_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the [] spelling' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
