# Readiness Ladder Discrimination Specification (defect class)

> Defect class: a readiness gate that admits everything (or nothing) passes a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Readiness Ladder Discrimination Specification (defect class)

Defect class: a readiness gate that admits everything (or nothing) passes a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/aspect_readiness_discrimination_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Defect class: a readiness gate that admits everything (or nothing) passes a
naive test while being useless. Every rejection here is paired with a
POSITIVE CONTROL at the SAME bar, and discrimination is proven between
ADJACENT rungs (none|boundary and boundary|full), not just top vs bottom.

## Scenarios

### Overstated claims fail closed while evidenced claims are accepted

#### adjacent rung none|boundary: a boundary claim with zero slots is REJECTED, the same claim with slots is ACCEPTED

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- adjacent rung none|boundary: a boundary claim with zero slots is REJECTED, the same claim with slots is ACCEPTED


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adjacent rung none|boundary: a boundary claim with zero slots is REJECTED, the same claim with slots is ACCEPTED")
expect readiness_declare("d.mod_a", READINESS_BOUNDARY, 0, 0) == false
expect readiness_last_error() == "claim 'boundary' unsupported: no cold-boundary slots"
expect readiness_level("d.mod_a") == ""
# positive control at the same bar
expect readiness_declare("d.mod_a", READINESS_BOUNDARY, 3, 0) == true
expect readiness_level("d.mod_a") == READINESS_BOUNDARY
```

</details>

#### adjacent rung boundary|full: a full claim with slots but zero patchable sites is REJECTED, with sites it is ACCEPTED

- adjacent rung boundary|full: a full claim with slots but zero patchable sites is REJECTED, with sites it is ACCEPTED


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adjacent rung boundary|full: a full claim with slots but zero patchable sites is REJECTED, with sites it is ACCEPTED")
expect readiness_declare("d.mod_b", READINESS_FULL, 8, 0) == false
expect readiness_last_error() == "claim 'full' unsupported: needs boundary slots and patchable sites"
# positive control at the same bar
expect readiness_declare("d.mod_b", READINESS_FULL, 8, 55) == true
expect readiness_level("d.mod_b") == READINESS_FULL
```

</details>

### The gate discriminates between adjacent rungs

#### the SAME requirement (boundary) rejects a none module and accepts a boundary module

- the SAME requirement (boundary) rejects a none module and accepts a boundary module


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the SAME requirement (boundary) rejects a none module and accepts a boundary module")
expect readiness_declare("d.none_mod", READINESS_NONE, 0, 0) == true
expect readiness_declare("d.bnd_mod", READINESS_BOUNDARY, 2, 0) == true
expect readiness_admits("d.none_mod", READINESS_BOUNDARY) == false
expect readiness_absence("d.none_mod", READINESS_BOUNDARY) == READINESS_NEEDS_REBUILD
expect readiness_admits("d.bnd_mod", READINESS_BOUNDARY) == true
```

</details>

#### the SAME requirement (full) rejects a boundary module and accepts a full module — with distinct typed reasons per rung below

- the SAME requirement (full) rejects a boundary module and accepts a full module — with distinct typed reasons per rung below


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the SAME requirement (full) rejects a boundary module and accepts a full module — with distinct typed reasons per rung below")
expect readiness_declare("d.bnd2_mod", READINESS_BOUNDARY, 2, 0) == true
expect readiness_declare("d.full_mod", READINESS_FULL, 2, 40) == true
expect readiness_admits("d.bnd2_mod", READINESS_FULL) == false
expect readiness_absence("d.bnd2_mod", READINESS_FULL) == READINESS_NEEDS_INSTRUMENTED_BUILD
expect readiness_admits("d.full_mod", READINESS_FULL) == true
# the two rejection reasons below full are distinct claims, not one blob
expect readiness_declare("d.none2_mod", READINESS_NONE, 0, 0) == true
expect readiness_absence("d.none2_mod", READINESS_FULL) == READINESS_NEEDS_REBUILD
```

</details>

### Promotion cannot pass on assertion alone

#### an evidence-free promotion is REJECTED and the level is unchanged; the evidenced one is ACCEPTED

- an evidence-free promotion is REJECTED and the level is unchanged; the evidenced one is ACCEPTED


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an evidence-free promotion is REJECTED and the level is unchanged; the evidenced one is ACCEPTED")
expect readiness_declare("d.promo", READINESS_BOUNDARY, 5, 0) == true
expect readiness_promote("d.promo", READINESS_FULL, 5, 0) == false
expect readiness_last_error() == "promotion to 'full' unsupported: insufficient evidence"
expect readiness_level("d.promo") == READINESS_BOUNDARY
expect readiness_admits("d.promo", READINESS_FULL) == false
# positive control
expect readiness_promote("d.promo", READINESS_FULL, 5, 70) == true
expect readiness_admits("d.promo", READINESS_FULL) == true
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

- Canonical SPipe generation for source `eceae946aa15b2f74b149359e47bc36a704b26a093bcf93aa48dc884a50e8cf4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eceae946aa15b2f74b149359e47bc36a704b26a093bcf93aa48dc884a50e8cf4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eceae946aa15b2f74b149359e47bc36a704b26a093bcf93aa48dc884a50e8cf4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/aspect_readiness_discrimination_spec.spl
mirror: doc/06_spec/01_unit/lib/aspect_readiness_discrimination_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/aspect_readiness_discrimination_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/aspect_readiness_discrimination_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/aspect_readiness_discrimination_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adjacent rung none|boundary: a boundary claim with zero slots is REJECTED, the same claim with slots is ACCEPTED' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/aspect_readiness_discrimination_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adjacent rung boundary|full: a full claim with slots but zero patchable sites is REJECTED, with sites it is ACCEPTED' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/aspect_readiness_discrimination_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the SAME requirement (boundary) rejects a none module and accepts a boundary module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
