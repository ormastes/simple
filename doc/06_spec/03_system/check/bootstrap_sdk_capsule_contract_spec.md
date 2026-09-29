# Bootstrap Sdk Capsule Contract Specification

> Tests covering Bootstrap SDK capsule contract, CAPSULE-001: canonical interfaces, CAPSULE-002: manifest identity, CAPSULE-003: target and source identity, CAPSULE-004: entry point and modules, CAPSULE-005: module imports and exports, CAPSULE-006: ABI surface, CAPSULE-007: deterministic body archive, CAPSULE-008: compiler and runtime provenance, CAPSULE-009: command host and source provenance, CAPSULE-010: artifact digest binding, CAPSULE-011: preparation claim boundary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Sdk Capsule Contract Specification

## Scenarios

### Bootstrap SDK capsule contract

### CAPSULE-001: canonical interfaces

#### should expose all four canonical interfaces

- should expose all four canonical interfaces
- Load the bootstrap SDK contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose all four canonical interfaces")
step("Load the bootstrap SDK contract")
val contract = step_bootstrap_sdk_contract()
expect(contract).to_contain("interface:BootstrapSdkManifest")
expect(contract).to_contain("interface:BootstrapSdkModuleInterface")
expect(contract).to_contain("interface:BootstrapSdkBodyArchive")
expect(contract).to_contain("interface:BootstrapSdkProvenance")
```

</details>

### CAPSULE-002: manifest identity

#### should identify the capsule manifest

- should identify the capsule manifest
- Check the manifest identity requirement


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should identify the capsule manifest")
step("Check the manifest identity requirement")
val contract = step_bootstrap_sdk_contract()
expect(contract).to_contain("SDK-001")
```

</details>

### CAPSULE-003: target and source identity

#### should bind target and source identity

- should bind target and source identity
- Check target and source identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bind target and source identity")
step("Check target and source identity")
val contract = step_bootstrap_sdk_contract()
expect(contract).to_contain("SDK-002")
```

</details>

### CAPSULE-004: entry point and modules

#### should declare the entry point and module set

- should declare the entry point and module set
- Check entry point and module declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should declare the entry point and module set")
step("Check entry point and module declarations")
val contract = step_bootstrap_sdk_contract()
expect(contract).to_contain("SDK-003")
```

</details>

### CAPSULE-005: module imports and exports

#### should expose module imports and exports

- should expose module imports and exports
- Check module interface boundaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose module imports and exports")
step("Check module interface boundaries")
val contract = step_bootstrap_sdk_contract()
expect(contract).to_contain("SDK-004")
```

</details>

### CAPSULE-006: ABI surface

#### should record ABI-relevant module surface

- should record ABI-relevant module surface
- Check ABI-relevant interface data


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should record ABI-relevant module surface")
step("Check ABI-relevant interface data")
val contract = step_bootstrap_sdk_contract()
expect(contract).to_contain("SDK-005")
```

</details>

### CAPSULE-007: deterministic body archive

#### should preserve ordered body digests

- should preserve ordered body digests
- Check deterministic body archive data


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve ordered body digests")
step("Check deterministic body archive data")
val contract = step_bootstrap_sdk_contract()
expect(contract).to_contain("SDK-006")
```

</details>

### CAPSULE-008: compiler and runtime provenance

#### should record compiler and runtime identity

- should record compiler and runtime identity
- Check compiler and runtime provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should record compiler and runtime identity")
step("Check compiler and runtime provenance")
val contract = step_bootstrap_sdk_contract()
expect(contract).to_contain("SDK-007")
```

</details>

### CAPSULE-009: command host and source provenance

#### should bind command host and source identity

- should bind command host and source identity
- Check command and host provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bind command host and source identity")
step("Check command and host provenance")
val contract = step_bootstrap_sdk_contract()
expect(contract).to_contain("SDK-008")
```

</details>

### CAPSULE-010: artifact digest binding

#### should bind artifact digests to provenance

- should bind artifact digests to provenance
- Check artifact digest binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bind artifact digests to provenance")
step("Check artifact digest binding")
val contract = step_bootstrap_sdk_contract()
expect(contract).to_contain("SDK-009")
```

</details>

### CAPSULE-011: preparation claim boundary

#### should publish only explicit false claim fields

- should publish only explicit false claim fields
- Check the preparation claim boundary
   - Expected: sdk_true_marker_allowed("reproducibility_evidence=true") is false
   - Expected: sdk_true_marker_allowed("stage4_admission_pass=true") is false
   - Expected: sdk_true_marker_allowed("platform_acceptance=true") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should publish only explicit false claim fields")
step("Check the preparation claim boundary")
val contract = step_bootstrap_sdk_contract()
expect(contract).to_contain("SDK-010")
expect(contract).to_contain("reproducibility_evidence=false")
expect(contract).to_contain("stage4_admission_pass=false")
expect(contract).to_contain("platform_acceptance=false")
expect(sdk_true_marker_allowed("reproducibility_evidence=true")).to_equal(false)
expect(sdk_true_marker_allowed("stage4_admission_pass=true")).to_equal(false)
expect(sdk_true_marker_allowed("platform_acceptance=true")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/bootstrap_sdk_capsule_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Bootstrap SDK capsule contract, CAPSULE-001: canonical interfaces, CAPSULE-002: manifest identity, CAPSULE-003: target and source identity, CAPSULE-004: entry point and modules, CAPSULE-005: module imports and exports, CAPSULE-006: ABI surface, CAPSULE-007: deterministic body archive, CAPSULE-008: compiler and runtime provenance, CAPSULE-009: command host and source provenance, CAPSULE-010: artifact digest binding, CAPSULE-011: preparation claim boundary.
- Bootstrap SDK capsule contract
- CAPSULE-001: canonical interfaces
- CAPSULE-002: manifest identity
- CAPSULE-003: target and source identity
- CAPSULE-004: entry point and modules
- CAPSULE-005: module imports and exports
- CAPSULE-006: ABI surface
- CAPSULE-007: deterministic body archive
- CAPSULE-008: compiler and runtime provenance
- CAPSULE-009: command host and source provenance
- CAPSULE-010: artifact digest binding
- CAPSULE-011: preparation claim boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `75d2d2f1b8204981a5483d0fc25e952e8095d8f22f0f147cd2f7dc4cfafb5564`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `75d2d2f1b8204981a5483d0fc25e952e8095d8f22f0f147cd2f7dc4cfafb5564`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `75d2d2f1b8204981a5483d0fc25e952e8095d8f22f0f147cd2f7dc4cfafb5564`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/check/bootstrap_sdk_capsule_contract_spec.spl
mirror: doc/06_spec/03_system/check/bootstrap_sdk_capsule_contract_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/bootstrap_sdk_capsule_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/bootstrap_sdk_capsule_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/bootstrap_sdk_capsule_contract_spec.spl:43:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose all four canonical interfaces' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/bootstrap_sdk_capsule_contract_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose all four canonical interfaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/bootstrap_sdk_capsule_contract_spec.spl:54:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should identify the capsule manifest' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/bootstrap_sdk_capsule_contract_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should identify the capsule manifest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/bootstrap_sdk_capsule_contract_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind target and source identity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/bootstrap_sdk_capsule_contract_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should bind target and source identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/bootstrap_sdk_capsule_contract_spec.spl:70:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should declare the entry point and module set' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/bootstrap_sdk_capsule_contract_spec.spl:78:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose module imports and exports' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/bootstrap_sdk_capsule_contract_spec.spl:86:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should record ABI-relevant module surface' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
