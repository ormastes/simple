# Backend Emulation Specification

> Tests covering Backend emulation lanes — DirectX software emulation and Metal availability.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Emulation Specification

## Scenarios

### Backend emulation lanes — DirectX software emulation and Metal availability

#### directx software-emulation lane (Linux compatibility path)

#### initializes via explicit request and reports an honest name

- initializes via explicit request and reports an honest name
   - Expected: probe.is_ok() is true
   - Expected: honest is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("initializes via explicit request and reports an honest name")
val probe = Engine2D.probe_backend(1, 1, "directx")
# Either windows-native "directx" or the honest Linux
# "directx-software-emulation" — both are initialized lanes.
expect(probe.is_ok()).to_equal(true)
var engine = Engine2D.create_with_backend(8, 8, "directx")
val name = engine.backend_name()
val honest = name == "directx" or name == "directx-software-emulation"
expect(honest).to_equal(true)
engine.shutdown()
```

</details>

#### matches the cpu reference pixel-for-pixel on the core scene

- matches the cpu reference pixel-for-pixel on the core scene
   - Expected: dx.len() equals `reference.len()`
   - Expected: emu_pixels_equal(dx, reference) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the cpu reference pixel-for-pixel on the core scene")
val reference = render_emulation_scene("cpu")
val dx = render_emulation_scene("directx")
expect(dx.len()).to_equal(reference.len())
expect(emu_pixels_equal(dx, reference)).to_equal(true)
```

</details>

#### deep viability probe never claims init_failed for the honest rename

- deep viability probe never claims init_failed for the honest rename
   - Expected: deep.reason does not contain `init_failed`
   - Expected: deep.reason contains `software_emulation`
   - Expected: deep.reason does not contain `fell back`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("deep viability probe never claims init_failed for the honest rename")
var engine = Engine2D.create_with_backend(8, 8, "directx")
val created = engine.backend_name()
engine.shutdown()
val deep = Engine2D.probe_backend_viable("directx")
if created == "directx-software-emulation":
    # Honest software lane: auto-resolve may defer to CPU lanes,
    # but the reason must state software emulation, not a lie
    # about a failed init.
    expect(deep.reason.contains("init_failed")).to_equal(false)
    expect(deep.reason.contains("software_emulation")).to_equal(true)
else:
    # Windows native lane: probe outcome is host-dependent; only
    # require that a rejection is not blamed on a fallback that
    # did not happen.
    expect(deep.reason.contains("fell back")).to_equal(false)
```

</details>

#### metal availability (no Linux emulation lane exists)

#### reports the exact macOS gate evidence when unavailable

- reports the exact macOS gate evidence when unavailable
   - Expected: probe.backend_name equals `metal`
   - Expected: probe.reason contains `Metal requires macOS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports the exact macOS gate evidence when unavailable")
val probe = Engine2D.probe_backend(1, 1, "metal")
if probe.is_ok():
    # macOS host: lane is real, nothing to gate here.
    expect(probe.backend_name).to_equal("metal")
else:
    expect(probe.reason.contains("Metal requires macOS")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/backend_emulation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Backend emulation lanes — DirectX software emulation and Metal availability.
- Backend emulation lanes — DirectX software emulation and Metal availability

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ce463cf43254e2972edbc87912256648087b78001574b7d514e68de17a27c827`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ce463cf43254e2972edbc87912256648087b78001574b7d514e68de17a27c827`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ce463cf43254e2972edbc87912256648087b78001574b7d514e68de17a27c827`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/rendering/backend_emulation_spec.spl
mirror: doc/06_spec/02_integration/rendering/backend_emulation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/backend_emulation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/backend_emulation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/backend_emulation_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'initializes via explicit request and reports an honest name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/backend_emulation_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the cpu reference pixel-for-pixel on the core scene' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/backend_emulation_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'deep viability probe never claims init_failed for the honest rename' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
