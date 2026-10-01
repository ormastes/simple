# Rv64 Production Wm Adapter Specification

> Tests covering RV64 production WM ownership adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rv64 Production Wm Adapter Specification

## Scenarios

### RV64 production WM ownership adapter

#### correlates a live process to its first Engine2D present

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- correlates a live process to its first Engine2D present
   - Expected: verdict.ready is true
   - Expected: verdict.failed is false
   - Expected: verdict.process_id equals `41u64`
   - Expected: verdict.first_present_revision equals `7`
   - Expected: verdict.reason equals `wm-process-owned-frame-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("correlates a live process to its first Engine2D present")
var adapter = Rv64ProductionWmAdapter.create(41u64)
adapter.observe_process(live_process(41u64))
val receipt = rv64_wm_engine2d_present_receipt(41u64, 41u64, 7, 7)
adapter.observe_first_present(receipt)
val verdict = adapter.verdict()
expect(verdict.ready).to_equal(true)
expect(verdict.failed).to_equal(false)
expect(verdict.process_id).to_equal(41u64)
expect(verdict.first_present_revision).to_equal(7)
expect(verdict.reason).to_equal("wm-process-owned-frame-ready")
```

</details>

#### fails when presentation arrives before process liveness

- fails when presentation arrives before process liveness
   - Expected: verdict.ready is false
   - Expected: verdict.failed is true
   - Expected: verdict.reason equals `present-before-process-live`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails when presentation arrives before process liveness")
var adapter = Rv64ProductionWmAdapter.create(41u64)
adapter.observe_first_present(rv64_wm_engine2d_present_receipt(41u64, 41u64, 7, 7))
val verdict = adapter.verdict()
expect(verdict.ready).to_equal(false)
expect(verdict.failed).to_equal(true)
expect(verdict.reason).to_equal("present-before-process-live")
```

</details>

#### fails an owner mismatch before readiness

- fails an owner mismatch before readiness
   - Expected: verdict.ready is false
   - Expected: verdict.failed is true
   - Expected: verdict.reason equals `window-owner-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails an owner mismatch before readiness")
var adapter = Rv64ProductionWmAdapter.create(41u64)
adapter.observe_process(live_process(41u64))
adapter.observe_first_present(rv64_wm_engine2d_present_receipt(41u64, 99u64, 7, 7))
val verdict = adapter.verdict()
expect(verdict.ready).to_equal(false)
expect(verdict.failed).to_equal(true)
expect(verdict.reason).to_equal("window-owner-mismatch")
```

</details>

#### fails an Engine2D revision mismatch before readiness

- fails an Engine2D revision mismatch before readiness
   - Expected: verdict.ready is false
   - Expected: verdict.failed is true
   - Expected: verdict.reason equals `present-revision-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails an Engine2D revision mismatch before readiness")
var adapter = Rv64ProductionWmAdapter.create(41u64)
adapter.observe_process(live_process(41u64))
adapter.observe_first_present(rv64_wm_engine2d_present_receipt(41u64, 41u64, 7, 6))
val verdict = adapter.verdict()
expect(verdict.ready).to_equal(false)
expect(verdict.failed).to_equal(true)
expect(verdict.reason).to_equal("present-revision-mismatch")
```

</details>

#### fails a duplicate first-present receipt

- fails a duplicate first-present receipt
   - Expected: verdict.ready is false
   - Expected: verdict.failed is true
   - Expected: verdict.reason equals `duplicate-present-receipt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails a duplicate first-present receipt")
var adapter = Rv64ProductionWmAdapter.create(41u64)
adapter.observe_process(live_process(41u64))
val receipt = rv64_wm_engine2d_present_receipt(41u64, 41u64, 7, 7)
adapter.observe_first_present(receipt)
adapter.observe_first_present(receipt)
val verdict = adapter.verdict()
expect(verdict.ready).to_equal(false)
expect(verdict.failed).to_equal(true)
expect(verdict.reason).to_equal("duplicate-present-receipt")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/wm/rv64_production_wm_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RV64 production WM ownership adapter.
- RV64 production WM ownership adapter

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `083069f8413031670f00bc147f7fe06ff07112e2a5868e3edaca443b7ebee13c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `083069f8413031670f00bc147f7fe06ff07112e2a5868e3edaca443b7ebee13c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `083069f8413031670f00bc147f7fe06ff07112e2a5868e3edaca443b7ebee13c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/wm/rv64_production_wm_adapter_spec.spl
mirror: doc/06_spec/01_unit/os/wm/rv64_production_wm_adapter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/wm/rv64_production_wm_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/wm/rv64_production_wm_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/wm/rv64_production_wm_adapter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/wm/rv64_production_wm_adapter_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'correlates a live process to its first Engine2D present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/wm/rv64_production_wm_adapter_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails when presentation arrives before process liveness' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/wm/rv64_production_wm_adapter_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails an owner mismatch before readiness' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
