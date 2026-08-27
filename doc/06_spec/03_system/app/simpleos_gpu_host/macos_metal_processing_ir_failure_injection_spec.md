# macos_metal_processing_ir_failure_injection_spec

> Prepared macOS live checks for Metal ProcessingIR failure injection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macos_metal_processing_ir_failure_injection_spec

Prepared macOS live checks for Metal ProcessingIR failure injection.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos_gpu_host/macos_metal_processing_ir_failure_injection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Prepared macOS live checks for Metal ProcessingIR failure injection.

## Scenarios

### prepared macOS Metal ProcessingIR failure injection

#### requires a macOS host for the live Metal executor

- requires a macOS host for the live Metal executor
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires a macOS host for the live Metal executor")
expect(is_macos()).to_equal(false)
pending("macOS Metal ProcessingIR live test is postponed to a macOS host")
```

</details>

#### proves the production default gate does not inject a failure

- proves the production default gate does not inject a failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("proves the production default gate does not inject a failure")
if _probe_mode(): return
expect(_assert_default_gate_absent()).to_contain(
    "fault_active=false completed=true reason=ok")
```

</details>

#### requires both fault gate variables

- requires both fault gate variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires both fault gate variables")
if _probe_mode(): return
expect(_run_case("init", true, false)).to_contain(
    "phase=init fault_active=false")
expect(_run_case("init", false, true)).to_contain(
    "phase=init fault_active=false")
```

</details>

#### returns typed init, submit, readback, and mismatch failures

- returns typed init, submit, readback, and mismatch failures


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns typed init, submit, readback, and mismatch failures")
if _probe_mode(): return
expect(_assert_injected("unavailable", "metal-unavailable")).to_contain(
    "reason=metal-unavailable")
expect(_assert_injected("init", "metal-init-failed")).to_contain(
    "reason=metal-init-failed")
_assert_injected("submit", "metal-submit-failed")
_assert_injected("readback", "metal-readback-failed")
_assert_injected("mismatch", "checksum-mismatch")
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ab75b5ca6ee0f606cc400cd021eddf37c6d329f9c0e67d58aef766330c795101`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ab75b5ca6ee0f606cc400cd021eddf37c6d329f9c0e67d58aef766330c795101`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ab75b5ca6ee0f606cc400cd021eddf37c6d329f9c0e67d58aef766330c795101`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/simpleos_gpu_host/macos_metal_processing_ir_failure_injection_spec.spl
mirror: doc/06_spec/03_system/app/simpleos_gpu_host/macos_metal_processing_ir_failure_injection_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos_gpu_host/macos_metal_processing_ir_failure_injection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos_gpu_host/macos_metal_processing_ir_failure_injection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos_gpu_host/macos_metal_processing_ir_failure_injection_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires a macOS host for the live Metal executor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos_gpu_host/macos_metal_processing_ir_failure_injection_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'proves the production default gate does not inject a failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos_gpu_host/macos_metal_processing_ir_failure_injection_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires both fault gate variables' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
