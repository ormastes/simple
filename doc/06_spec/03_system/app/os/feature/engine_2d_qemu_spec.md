# Engine 2d Qemu Specification

> Tests covering Engine2D QEMU graphics-core acceptance contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine 2d Qemu Specification

## Scenarios

### Engine2D QEMU graphics-core acceptance contract

#### requires BGA Engine2D verification markers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires BGA Engine2D verification markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires BGA Engine2D verification markers")
val serial = "[E2D] Engine2D verification frame painted\n" +
    "[E2D-PRIM] Engine2D primitive frame painted\n"
expect(_contains_all_markers(serial, [
    "[E2D] Engine2D verification frame painted",
    "[E2D-PRIM] Engine2D primitive frame painted"
])).to_equal(true)
```

</details>

#### requires WM Simple Web Engine2D markers

- requires WM Simple Web Engine2D markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires WM Simple Web Engine2D markers")
val serial = "[wm-demo] wm-service-ready\n" +
    "[e2d-demo] engine-core-ready\n" +
    "[web-demo] pixels-ready count=114400\n" +
    "[integrated-demo] render-ready\n"
expect(_contains_all_markers(serial, [
    "[wm-demo] wm-service-ready",
    "[e2d-demo] engine-core-ready",
    "[web-demo] pixels-ready",
    "[integrated-demo] render-ready"
])).to_equal(true)
```

</details>

#### keeps VirtIO-GPU as proof coverage

- keeps VirtIO-GPU as proof coverage
   - Expected: _contains_all_markers(serial, ["[gui-e2d-virtio] render-ready"]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps VirtIO-GPU as proof coverage")
val serial = "[gui-e2d-virtio] render-ready\n"
expect(_contains_all_markers(serial, ["[gui-e2d-virtio] render-ready"])).to_equal(true)
```

</details>

#### requires QMP PPM capture to be non-empty and non-black

- requires QMP PPM capture to be non-empty and non-black
   - Expected: _nonblack_ppm_contract(1024, 768, 1) is true
   - Expected: _nonblack_ppm_contract(1024, 768, 0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires QMP PPM capture to be non-empty and non-black")
expect(_nonblack_ppm_contract(1024, 768, 1)).to_equal(true)
expect(_nonblack_ppm_contract(1024, 768, 0)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/os/feature/engine_2d_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D QEMU graphics-core acceptance contract.
- Engine2D QEMU graphics-core acceptance contract

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

- Canonical SPipe generation for source `7f9128b9b7f4e9fa525cb819936a6b771d70ce2334198ee2cd3f42aff81b999d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7f9128b9b7f4e9fa525cb819936a6b771d70ce2334198ee2cd3f42aff81b999d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7f9128b9b7f4e9fa525cb819936a6b771d70ce2334198ee2cd3f42aff81b999d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/os/feature/engine_2d_qemu_spec.spl
mirror: doc/06_spec/03_system/app/os/feature/engine_2d_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/os/feature/engine_2d_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/os/feature/engine_2d_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/os/feature/engine_2d_qemu_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires BGA Engine2D verification markers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/os/feature/engine_2d_qemu_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires WM Simple Web Engine2D markers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/os/feature/engine_2d_qemu_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps VirtIO-GPU as proof coverage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
