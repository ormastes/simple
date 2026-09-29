# Std Hash Facade Specification

> Tests covering std.hash facade — trait half, std.hash facade — function half must not be dropped.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Std Hash Facade Specification

## Scenarios

### std.hash facade — trait half

#### resolves the Hash trait through `use std.hash`

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves the Hash trait through `use std.hash`
   - Expected: p.hash() equals `65`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves the Hash trait through `use std.hash`")
val p = FacadePoint(x: 2, y: 3)
expect(p.hash()).to_equal(65)
```

</details>

#### hashes text through the trait impl in hash.spl

- hashes text through the trait impl in hash.spl


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("hashes text through the trait impl in hash.spl")
val h = "abc".hash()
expect(h != 0).to_be_true()
```

</details>

#### exposes hash_combine

- exposes hash_combine


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exposes hash_combine")
val combined = hash_combine(1, 2)
expect(combined != 0).to_be_true()
```

</details>

### std.hash facade — function half must not be dropped

#### exposes hash_array

- exposes hash_array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exposes hash_array")
val h = hash_array([1, 2, 3])
expect(h != 0).to_be_true()
```

</details>

#### exposes rt_hash_text

- exposes rt_hash_text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exposes rt_hash_text")
val a = rt_hash_text("a")
val b = rt_hash_text("b")
expect(a != b).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std_hash_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering std.hash facade — trait half, std.hash facade — function half must not be dropped.
- std.hash facade — trait half
- std.hash facade — function half must not be dropped

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `855d7f8269ce268d1a796fd6f3afe00b7d28190a8937c981abaca726c0c3cd8e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `855d7f8269ce268d1a796fd6f3afe00b7d28190a8937c981abaca726c0c3cd8e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `855d7f8269ce268d1a796fd6f3afe00b7d28190a8937c981abaca726c0c3cd8e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/std_hash_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/std_hash_facade_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/std_hash_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/std_hash_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/std_hash_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/std_hash_facade_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves the Hash trait through `use std.hash`' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std_hash_facade_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hashes text through the trait impl in hash.spl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std_hash_facade_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes hash_combine' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
