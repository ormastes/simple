# Chained Method I64 Conversion Specification

> Tests covering chained two-hop method calls ending in to_i64() (interpreter oracle).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chained Method I64 Conversion Specification

## Scenarios

### chained two-hop method calls ending in to_i64() (interpreter oracle)

#### parses a single trimmed numeric string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses a single trimmed numeric string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a single trimmed numeric string")
assert_equal("  480  ".trim().to_i64(), 480)
```

</details>

#### parses two independent trimmed numeric strings in the same function

- parses two independent trimmed numeric strings in the same function


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses two independent trimmed numeric strings in the same function")
val pw = "480".trim().to_i64()
val ph = "360".trim().to_i64()
assert_equal(pw, 480)
assert_equal(ph, 360)
```

</details>

#### matches the exact motivating pattern: split + index + trim + to_i64

- matches the exact motivating pattern: split + index + trim + to_i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches the exact motivating pattern: split + index + trim + to_i64")
val parts = "480x360".split("x")
val pw = parts[0].trim().to_i64()
val ph = parts[1].trim().to_i64()
assert_equal(pw, 480)
assert_equal(ph, 360)
```

</details>

#### generalizes beyond trim(): any text-returning hop before to_i64()

- generalizes beyond trim(): any text-returning hop before to_i64()


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generalizes beyond trim(): any text-returning hop before to_i64()")
val pw = "480".lower().to_i64()
val ph = "360".lower().to_i64()
assert_equal(pw, 480)
assert_equal(ph, 360)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/language/chained_method_i64_conversion_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering chained two-hop method calls ending in to_i64() (interpreter oracle).
- chained two-hop method calls ending in to_i64() (interpreter oracle)

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `42dc0adf0494602ae0505954d81a301ff72548685c2c5f9c0116fc459767f8b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `42dc0adf0494602ae0505954d81a301ff72548685c2c5f9c0116fc459767f8b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `42dc0adf0494602ae0505954d81a301ff72548685c2c5f9c0116fc459767f8b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/language/chained_method_i64_conversion_spec.spl
mirror: doc/06_spec/01_unit/lib/language/chained_method_i64_conversion_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/language/chained_method_i64_conversion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/language/chained_method_i64_conversion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/language/chained_method_i64_conversion_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a single trimmed numeric string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/language/chained_method_i64_conversion_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses two independent trimmed numeric strings in the same function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/language/chained_method_i64_conversion_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the exact motivating pattern: split + index + trim + to_i64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
