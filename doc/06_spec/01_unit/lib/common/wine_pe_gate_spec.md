# Wine Pe Gate Specification

> Tests covering Wine PE loader gate, loader feature coverage, header classification, execution gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Pe Gate Specification

## Scenarios

### Wine PE loader gate

### loader feature coverage

#### lists PE validation features needed before hello.exe

- lists PE validation features needed before hello.exe
   - Expected: required[0] equals `mz`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists PE validation features needed before hello.exe")
val required = wine_pe_required_features()
expect(required.len()).to_be_greater_than(10)
expect(required[0]).to_equal("mz")
```

</details>

#### reports the first missing PE loader feature

- reports the first missing PE loader feature
   - Expected: state equals `missing-section-bounds`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the first missing PE loader feature")
val state = wine_pe_gate("mz pe-signature machine-x86_64 pe32plus")
expect(state).to_equal("missing-section-bounds")
```

</details>

#### returns ready for the full safe parse/map feature set

- returns ready for the full safe parse/map feature set
   - Expected: state equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns ready for the full safe parse/map feature set")
val state = wine_pe_gate("mz pe-signature machine-x86_64 pe32plus section-bounds console-subsystem imports relocations tls-directory structured-errors safe-map no-exec-before-gates")
expect(state).to_equal("ready")
```

</details>

#### derives PE readiness from actual image bytes and loader policies

- derives PE readiness from actual image bytes and loader policies
   - Expected: state equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives PE readiness from actual image bytes and loader policies")
val state = wine_pe_gate_from_image(_image(), "native-module-open tls-callback", "structured-errors safe-map no-exec-before-gates")
expect(state).to_equal("ready")
```

</details>

#### keeps image-backed PE readiness blocked on structured loader policy

- keeps image-backed PE readiness blocked on structured loader policy
   - Expected: wine_pe_gate_from_image(_image(), "native-module-open tls-callback", "structured-errors safe-map") equals `missing-no-exec-before-gates`
   - Expected: wine_pe_gate_from_image(_image(), "native-module-open", "structured-errors safe-map no-exec-before-gates") equals `missing-api-tls-callback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps image-backed PE readiness blocked on structured loader policy")
expect(wine_pe_gate_from_image(_image(), "native-module-open tls-callback", "structured-errors safe-map")).to_equal("missing-no-exec-before-gates")
expect(wine_pe_gate_from_image(_image(), "native-module-open", "structured-errors safe-map no-exec-before-gates")).to_equal("missing-api-tls-callback")
```

</details>

### header classification

#### rejects non-MZ inputs

- rejects non-MZ inputs
   - Expected: wine_pe_header_gate("not-pe") equals `bad-mz`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-MZ inputs")
expect(wine_pe_header_gate("not-pe")).to_equal("bad-mz")
```

</details>

#### accepts a declared PE32+ x86_64 console header summary

- accepts a declared PE32+ x86_64 console header summary
   - Expected: wine_pe_header_gate(summary) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a declared PE32+ x86_64 console header summary")
val summary = "MZ PE x86_64 PE32+ console"
expect(wine_pe_header_gate(summary)).to_equal("ready")
```

</details>

### execution gate

#### blocks execution until process, VM, host, and PE gates are verified

- blocks execution until process, VM, host, and PE gates are verified
   - Expected: state equals `blocked-host`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks execution until process, VM, host, and PE gates are verified")
val state = wine_pe_execution_gate("process=verified vm=verified host=partial pe=verified")
expect(state).to_equal("blocked-host")
```

</details>

#### requires async and thread gates before PE execution

- requires async and thread gates before PE execution
   - Expected: state equals `blocked-async`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires async and thread gates before PE execution")
val state = wine_pe_execution_gate("process=verified vm=verified host=verified posix=verified pthread=verified dynload=verified pe=verified")
expect(state).to_equal("blocked-async")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_pe_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine PE loader gate, loader feature coverage, header classification, execution gate.
- Wine PE loader gate
- loader feature coverage
- header classification
- execution gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `e96b40a62365aeea4177c6f37954e7590f7c176db73376e30f12d55a5a41360e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e96b40a62365aeea4177c6f37954e7590f7c176db73376e30f12d55a5a41360e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e96b40a62365aeea4177c6f37954e7590f7c176db73376e30f12d55a5a41360e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/wine_pe_gate_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_pe_gate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_pe_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_pe_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_pe_gate_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists PE validation features needed before hello.exe' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_pe_gate_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the first missing PE loader feature' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_pe_gate_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns ready for the full safe parse/map feature set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
