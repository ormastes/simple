# Provider Work Control Specification

> Tests covering SPipe provider bounded work control.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Provider Work Control Specification

## Scenarios

### SPipe provider bounded work control

#### charges a closed category before reaching its exact limit

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- charges a closed category before reaching its exact limit
   - Expected: budget.consumed(raw) equals `3`
   - Expected: budget.limit(raw) equals `4`
   - Expected: budget.consumed(raw) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("charges a closed category before reaching its exact limit")
val raw = provider_budget_category_raw_bytes()
var budget = ProviderBoundedBudgetV1.configured([
    ProviderBudgetLimitV1(category: raw, limit: 4)
])?
budget.charge(ProviderBudgetChargeV1(category: raw, amount: 3))?
expect(budget.consumed(raw)).to_equal(3)
expect(budget.limit(raw)).to_equal(4)
budget.charge(ProviderBudgetChargeV1(category: raw, amount: 1))?
expect(budget.consumed(raw)).to_equal(4)
```

</details>

#### rejects overflow unknown and duplicate categories without mutation

- rejects overflow unknown and duplicate categories without mutation
   - Expected: budget.consumed(blocks) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects overflow unknown and duplicate categories without mutation")
val blocks = provider_budget_category_hash_blocks()
var budget = ProviderBoundedBudgetV1.configured([
    ProviderBudgetLimitV1(category: blocks, limit: 2)
])?
expect(budget.charge(ProviderBudgetChargeV1(category: blocks,
    amount: 3)).is_err()).to_equal(true)
expect(budget.consumed(blocks)).to_equal(0)
expect(budget.charge(ProviderBudgetChargeV1(category: "invented",
    amount: 1)).is_err()).to_equal(true)
expect(ProviderBoundedBudgetV1.configured([
    ProviderBudgetLimitV1(category: blocks, limit: 1),
    ProviderBudgetLimitV1(category: blocks, limit: 2)
]).is_err()).to_equal(true)
```

</details>

#### admits a multi-category charge atomically after duplicate aggregation

- admits a multi-category charge atomically after duplicate aggregation
   - Expected: budget.consumed(raw) equals `6`
   - Expected: budget.consumed(output) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("admits a multi-category charge atomically after duplicate aggregation")
val raw = provider_budget_category_raw_bytes()
val output = provider_budget_category_output_bytes()
var budget = ProviderBoundedBudgetV1.configured([
    ProviderBudgetLimitV1(category: raw, limit: 8),
    ProviderBudgetLimitV1(category: output, limit: 8)
])?
budget.charge_all([
    ProviderBudgetChargeV1(category: raw, amount: 2),
    ProviderBudgetChargeV1(category: output, amount: 3),
    ProviderBudgetChargeV1(category: raw, amount: 4)
])?
expect(budget.consumed(raw)).to_equal(6)
expect(budget.consumed(output)).to_equal(3)
```

</details>

#### rejects a failing second category without charging the first

- rejects a failing second category without charging the first
   - Expected: budget.consumed(raw) equals `0`
   - Expected: budget.consumed(output) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a failing second category without charging the first")
val raw = provider_budget_category_raw_bytes()
val output = provider_budget_category_output_bytes()
var budget = ProviderBoundedBudgetV1.configured([
    ProviderBudgetLimitV1(category: raw, limit: 8),
    ProviderBudgetLimitV1(category: output, limit: 2)
])?
expect(budget.charge_all([
    ProviderBudgetChargeV1(category: raw, amount: 5),
    ProviderBudgetChargeV1(category: output, amount: 3)
]).is_err()).to_equal(true)
expect(budget.consumed(raw)).to_equal(0)
expect(budget.consumed(output)).to_equal(0)
```

</details>

#### fails closed for duplicate overflow invalid amounts and empty batches

- fails closed for duplicate overflow invalid amounts and empty batches
   - Expected: budget.consumed(raw) equals `0`
   - Expected: budget.charge_all([]).is_err() is true
   - Expected: budget.consumed(raw) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fails closed for duplicate overflow invalid amounts and empty batches")
val raw = provider_budget_category_raw_bytes()
var budget = ProviderBoundedBudgetV1.configured([
    ProviderBudgetLimitV1(category: raw, limit: 9223372036854775807)
])?
expect(budget.charge_all([
    ProviderBudgetChargeV1(category: raw,
        amount: 9223372036854775807),
    ProviderBudgetChargeV1(category: raw, amount: 1)
]).is_err()).to_equal(true)
expect(budget.consumed(raw)).to_equal(0)
expect(budget.charge_all([
    ProviderBudgetChargeV1(category: raw, amount: 0)
]).is_err()).to_equal(true)
expect(budget.charge_all([]).is_err()).to_equal(true)
expect(budget.consumed(raw)).to_equal(0)
```

</details>

#### fails budget and checkpoint operations closed after close

- fails budget and checkpoint operations closed after close
   - Expected: budget.consumed(raw) equals `0`
   - Expected: checkpoint.checkpoint(progress(1, 0)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fails budget and checkpoint operations closed after close")
val raw = provider_budget_category_raw_bytes()
var budget = ProviderBoundedBudgetV1.configured([
    ProviderBudgetLimitV1(category: raw, limit: 8)
])?
budget.close()
expect(budget.charge(ProviderBudgetChargeV1(category: raw,
    amount: 1)).is_err()).to_equal(true)
expect(budget.consumed(raw)).to_equal(0)

var checkpoint = ProviderDeterministicCheckpointV1.configured(
    request_handle(), progress(16, 1), -1, "")?
checkpoint.close()
expect(checkpoint.checkpoint(progress(1, 0)).is_err()).to_equal(true)
```

</details>

#### binds request identity once and enforces progress bounds

- binds request identity once and enforces progress bounds
   - Expected: checkpoint.bound_request().request_id equals `req-work-1`
   - Expected: checkpoint.checkpoint(progress(65, 2)).is_err() is true
   - Expected: checkpoint.checkpoint(progress(64, 3)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("binds request identity once and enforces progress bounds")
var checkpoint = ProviderDeterministicCheckpointV1.configured(
    request_handle(), progress(64, 2), -1, "")?
checkpoint.checkpoint(progress(64, 2))?
expect(checkpoint.bound_request().request_id).to_equal("req-work-1")
expect(checkpoint.checkpoint(progress(65, 2)).is_err()).to_equal(true)
expect(checkpoint.checkpoint(progress(64, 3)).is_err()).to_equal(true)
```

</details>

#### injects deterministic cancellation at an exact checkpoint boundary

- injects deterministic cancellation at an exact checkpoint boundary
   - Expected: checkpoint.checkpoint(progress(1, 0)).is_err() is true
   - Expected: provider_budget_category_valid_v1("invented") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("injects deterministic cancellation at an exact checkpoint boundary")
var checkpoint = ProviderDeterministicCheckpointV1.configured(
    request_handle(), progress(4096, 64), 1, "cancelled")?
checkpoint.checkpoint(progress(4096, 64))?
expect(checkpoint.checkpoint(progress(1, 0)).is_err()).to_equal(true)
expect(provider_budget_category_valid_v1("invented")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/spipe_knowledge_provider/provider_work_control_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SPipe provider bounded work control.
- SPipe provider bounded work control

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `39d276090eb7d3dd030a5e7fd16443b1109f608ea0bdb3488286f20ea6185f17`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `39d276090eb7d3dd030a5e7fd16443b1109f608ea0bdb3488286f20ea6185f17`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `39d276090eb7d3dd030a5e7fd16443b1109f608ea0bdb3488286f20ea6185f17`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/spipe_knowledge_provider/provider_work_control_spec.spl
mirror: doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_work_control_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_work_control_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_work_control_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/spipe_knowledge_provider/provider_work_control_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/spipe_knowledge_provider/provider_work_control_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'charges a closed category before reaching its exact limit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spipe_knowledge_provider/provider_work_control_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects overflow unknown and duplicate categories without mutation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spipe_knowledge_provider/provider_work_control_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits a multi-category charge atomically after duplicate aggregation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
