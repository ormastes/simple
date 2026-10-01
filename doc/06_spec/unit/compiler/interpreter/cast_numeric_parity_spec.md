# Numeric Cast Parity Specification

> Confirms that plain numeric casts and interpolation remain valid in the current

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Numeric Cast Parity Specification

Confirms that plain numeric casts and interpolation remain valid in the current

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/interpreter/cast_numeric_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Confirms that plain numeric casts and interpolation remain valid in the current
runtime, so dashboard assistant failures can be classified as a narrower
data-shape bug rather than a generic `as i64` language bug.

## Scenarios

### numeric cast parity

#### supports plain float to i64 cast

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- supports plain float to i64 cast
   - Expected: n as i64 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports plain float to i64 cast")
val n = 42.0
expect(n as i64).to_equal(42)
```

</details>

#### supports plain float cast inside interpolation

- supports plain float cast inside interpolation
   - Expected: "{n as i64}" equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports plain float cast inside interpolation")
val n = 42.0
expect("{n as i64}").to_equal("42")
```

</details>

#### supports json-derived number to i64 cast

- supports json-derived number to i64 cast
   - Expected: n as i64 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports json-derived number to i64 cast")
val arr = json_parse("[42]")
val raw = json_array_get(arr, 0)
val n = json_to_number(raw)
expect(n as i64).to_equal(42)
```

</details>

#### supports json-derived number cast inside interpolation

- supports json-derived number cast inside interpolation
   - Expected: "{n as i64}" equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports json-derived number cast inside interpolation")
val arr = json_parse("[42]")
val raw = json_array_get(arr, 0)
val n = json_to_number(raw)
expect("{n as i64}").to_equal("42")
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f20f6c5137dd085e9e161459bf0175d5691d4a533ffc66eeb5dc9c00c1eb9c6f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f20f6c5137dd085e9e161459bf0175d5691d4a533ffc66eeb5dc9c00c1eb9c6f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f20f6c5137dd085e9e161459bf0175d5691d4a533ffc66eeb5dc9c00c1eb9c6f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/interpreter/cast_numeric_parity_spec.spl
mirror: doc/06_spec/unit/compiler/interpreter/cast_numeric_parity_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/interpreter/cast_numeric_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/interpreter/cast_numeric_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/interpreter/cast_numeric_parity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/interpreter/cast_numeric_parity_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports plain float to i64 cast' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/interpreter/cast_numeric_parity_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports plain float cast inside interpolation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/interpreter/cast_numeric_parity_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports json-derived number to i64 cast' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
