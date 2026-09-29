# math_bridge_stats_spec

> Reproducing spec for the `variance_sample` import that never existed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# math_bridge_stats_spec

Reproducing spec for the `variance_sample` import that never existed.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/math_bridge_stats_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Reproducing spec for the `variance_sample` import that never existed.

`math_bridge.spl` imported `variance_sample` from `std.common.math.statistics`
and called it from `excel_var`. No such symbol is exported — the real name is
`var_sample` — so the whole module failed to resolve and every Excel statistics
function in Calc was unreachable, not merely wrong.

Ground truth is hand-computable. For `[2, 4, 4, 4, 5, 5, 7, 9]`:
mean = 5, sum of squared deviations = 32, sample variance = 32 / 7.

## Scenarios

### math_bridge Excel statistics reach the stdlib

#### excel_var is the SAMPLE variance (n-1 denominator)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- excel_var is the SAMPLE variance (n-1 denominator)
   - Expected: _close(excel_var(_sample()), 32.0 / 7.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("excel_var is the SAMPLE variance (n-1 denominator)")
expect(_close(excel_var(_sample()), 32.0 / 7.0)).to_equal(true)
```

</details>

#### excel_var is not the POPULATION variance

- excel_var is not the POPULATION variance
   - Expected: _close(excel_var(_sample()), 32.0 / 8.0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("excel_var is not the POPULATION variance")
expect(_close(excel_var(_sample()), 32.0 / 8.0)).to_equal(false)
```

</details>

#### excel_stdev is the square root of excel_var

- excel_stdev is the square root of excel_var
   - Expected: _close(s * s, v) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("excel_stdev is the square root of excel_var")
val v = excel_var(_sample())
val s = excel_stdev(_sample())
expect(_close(s * s, v)).to_equal(true)
```

</details>

#### excel_median returns the middle of the sorted sample

- excel_median returns the middle of the sorted sample
   - Expected: _close(excel_median(_sample()), 4.5) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("excel_median returns the middle of the sorted sample")
expect(_close(excel_median(_sample()), 4.5)).to_equal(true)
```

</details>

#### a sample of one has zero sample variance rather than dividing by zero

- a sample of one has zero sample variance rather than dividing by zero
   - Expected: _close(excel_var([3.0]), 0.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a sample of one has zero sample variance rather than dividing by zero")
expect(_close(excel_var([3.0]), 0.0)).to_equal(true)
```

</details>

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

- Canonical SPipe generation for source `18907eebec542a38b7158489e72ca57254b0a9fc6a198755c1e821e5ce1cd203`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `18907eebec542a38b7158489e72ca57254b0a9fc6a198755c1e821e5ce1cd203`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `18907eebec542a38b7158489e72ca57254b0a9fc6a198755c1e821e5ce1cd203`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/math_bridge_stats_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/math_bridge_stats_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/math_bridge_stats_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/math_bridge_stats_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/math_bridge_stats_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'excel_var is the SAMPLE variance (n-1 denominator)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/math_bridge_stats_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'excel_var is not the POPULATION variance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/math_bridge_stats_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'excel_stdev is the square root of excel_var' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
