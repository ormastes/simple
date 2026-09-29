# Option I64 Value3 Sentinel Specification

> Tests covering i64? payload-3 vs nil (interpreter lane).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Option I64 Value3 Sentinel Specification

## Scenarios

### i64? payload-3 vs nil (interpreter lane)

#### Some(3) is not nil

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Some(3) is not nil
   - Expected: a == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("Some(3) is not nil")
val a: i64? = 3
expect(a == nil).to_equal(false)
```

</details>

#### Some(3) unwraps to 3 via ??, not the default

- Some(3) unwraps to 3 via ??, not the default
   - Expected: u equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("Some(3) unwraps to 3 via ??, not the default")
val a: i64? = 3
val u = a ?? -1
expect(u).to_equal(3)
```

</details>

#### nil is still nil

- nil is still nil
   - Expected: b == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("nil is still nil")
val b: i64? = nil
expect(b == nil).to_equal(true)
```

</details>

#### nil unwraps to the default via ??

- nil unwraps to the default via ??
   - Expected: v equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("nil unwraps to the default via ??")
val b: i64? = nil
val v = b ?? -1
expect(v).to_equal(-1)
```

</details>

#### non-collision payloads round-trip too (sanity band around 3)

- non-collision payloads round-trip too (sanity band around 3)
   - Expected: opt == nil is false
   - Expected: opt ?? -99 equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("non-collision payloads round-trip too (sanity band around 3)")
val vals: List<i64> = [0, 1, 2, 3, 4, 11]
for x in vals:
    val opt: i64? = x
    expect(opt == nil).to_equal(false)
    expect(opt ?? -99).to_equal(x)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/language/option_i64_value3_sentinel_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering i64? payload-3 vs nil (interpreter lane).
- i64? payload-3 vs nil (interpreter lane)

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

- `REQ-SSPEC-LANGUAGE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `feb2ca95649da45ff2d36969e7d90c553b08809fa4e62222e8024be04600e93c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `feb2ca95649da45ff2d36969e7d90c553b08809fa4e62222e8024be04600e93c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `feb2ca95649da45ff2d36969e7d90c553b08809fa4e62222e8024be04600e93c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/language/option_i64_value3_sentinel_spec.spl
mirror: doc/06_spec/01_unit/language/option_i64_value3_sentinel_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/language/option_i64_value3_sentinel_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/language/option_i64_value3_sentinel_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/language/option_i64_value3_sentinel_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/language/option_i64_value3_sentinel_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Some(3) is not nil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/option_i64_value3_sentinel_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Some(3) unwraps to 3 via ??, not the default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/option_i64_value3_sentinel_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'nil is still nil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
