# Wine Image Vm Map Specification

> Tests covering Wine PE image to VM process mapping.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Image Vm Map Specification

## Scenarios

### Wine PE image to VM process mapping

#### rejects malformed PE before touching the VM process

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects malformed PE before touching the VM process
   - Expected: result.ok is false
   - Expected: result.state equals `too-small`
   - Expected: result.space.regions.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects malformed PE before touching the VM process")
val space = wine_vm_process_space_new(10, 9000, "pid fs ipc net capability")
val result = wine_image_map_into_vm_process([], space, 0x400000, 0x700000, 0x2000, 0x1000)
expect(result.ok).to_equal(false)
expect(result.state).to_equal("too-small")
expect(result.space.regions.len()).to_equal(0)
```

</details>

#### maps a validated image and stack into an OS-backed VM process

- maps a validated image and stack into an OS-backed VM process
   - Expected: result.ok is true
   - Expected: result.state equals `mapped`
   - Expected: result.entry_address equals `0x402010`
   - Expected: result.space.regions.len() equals `3`
   - Expected: wine_vm_production_gate(result.space, _fault()) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps a validated image and stack into an OS-backed VM process")
val space = wine_vm_process_space_new(10, 9000, "pid fs ipc net capability")
val result = wine_image_map_into_vm_process(_minimal_image(0x2010, 0x5000), space, 0x400000, 0x700000, 0x2000, 0x1000)
expect(result.ok).to_equal(true)
expect(result.state).to_equal("mapped")
expect(result.entry_address).to_equal(0x402010)
expect(result.space.regions.len()).to_equal(3)
expect(wine_vm_production_gate(result.space, _fault())).to_equal("ready")
```

</details>

#### rejects overlapping image and stack ranges

- rejects overlapping image and stack ranges
   - Expected: result.ok is false
   - Expected: result.state equals `fixed-map-conflict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects overlapping image and stack ranges")
val space = wine_vm_process_space_new(10, 9000, "pid fs ipc net capability")
val result = wine_image_map_into_vm_process(_minimal_image(0x2010, 0x5000), space, 0x400000, 0x401000, 0x2000, 0x1000)
expect(result.ok).to_equal(false)
expect(result.state).to_equal("fixed-map-conflict")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_image_vm_map_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine PE image to VM process mapping.
- Wine PE image to VM process mapping

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9d9cec71d63e4fa8f1ea7422687e5d11a68c6f18786e595f1082d91fe92cc10c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9d9cec71d63e4fa8f1ea7422687e5d11a68c6f18786e595f1082d91fe92cc10c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9d9cec71d63e4fa8f1ea7422687e5d11a68c6f18786e595f1082d91fe92cc10c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/wine_image_vm_map_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_image_vm_map_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_image_vm_map_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_image_vm_map_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_image_vm_map_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_image_vm_map_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects malformed PE before touching the VM process' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_image_vm_map_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps a validated image and stack into an OS-backed VM process' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_image_vm_map_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects overlapping image and stack ranges' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
