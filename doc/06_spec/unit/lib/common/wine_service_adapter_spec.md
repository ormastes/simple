# Wine Service Adapter Specification

> Tests covering Wine host service adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Service Adapter Specification

## Scenarios

### Wine host service adapter

#### lists IPC, handle, audio, font, crypto, HID, printing, and multimedia services

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lists IPC, handle, audio, font, crypto, HID, printing, and multimedia services
   - Expected: services[0] equals `ipc-server`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists IPC, handle, audio, font, crypto, HID, printing, and multimedia services")
val services = wine_service_adapter_required_services()
expect(services.len()).to_be_greater_than(10)
expect(services[0]).to_equal("ipc-server")
```

</details>

#### reports the first missing service

- reports the first missing service
   - Expected: missing[0] equals `audio-device`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the first missing service")
val missing = wine_service_adapter_missing_services("ipc-server handle-table")
expect(missing[0]).to_equal("audio-device")
```

</details>

#### rejects unknown service declarations

- rejects unknown service declarations
   - Expected: result.ok is false
   - Expected: result.state equals `unknown-service`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unknown service declarations")
val result = wine_service_adapter_add(wine_service_adapter_new(_base_host_features()), "unknown")
expect(result.ok).to_equal(false)
expect(result.state).to_equal("unknown-service")
```

</details>

#### derives host features only from complete service pairs

- derives host features only from complete service pairs
   - Expected: partial equals `_base_host_features()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives host features only from complete service pairs")
val partial = wine_service_adapter_feature_string("audio-device font-discovery crypto-random hid-keyboard", _base_host_features())
expect(partial).to_equal(_base_host_features())

val full = wine_service_adapter_feature_string(_all_services(), _base_host_features())
expect(full).to_contain("audio")
expect(full).to_contain("fonts")
expect(full).to_contain("crypto")
expect(full).to_contain("hid")
```

</details>

#### blocks on missing service coverage before host readiness

- blocks on missing service coverage before host readiness
   - Expected: wine_service_adapter_gate(added.adapter) equals `missing-service-handle-table`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks on missing service coverage before host readiness")
val adapter = wine_service_adapter_new(_base_host_features())
val added = wine_service_adapter_add(adapter, "ipc-server")
expect(wine_service_adapter_gate(added.adapter)).to_equal("missing-service-handle-table")
```

</details>

#### reaches the existing host gate when all service and base features are present

- reaches the existing host gate when all service and base features are present
   - Expected: wine_service_adapter_gate(adapter) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reaches the existing host gate when all service and base features are present")
val adapter = wine_service_adapter_ready(_base_host_features())
expect(wine_service_adapter_gate(adapter)).to_equal("ready")
```

</details>

#### requires bounded ADVAPI32 service-control evidence before service readiness

- requires bounded ADVAPI32 service-control evidence before service readiness
   - Expected: wine_service_adapter_gate_with_service_result(adapter, service) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires bounded ADVAPI32 service-control evidence before service readiness")
val adapter = wine_service_adapter_ready(_base_host_features())
val service = wine_advapi32_execute_service_start(
    ["OpenSCManagerW", "CreateServiceW", "OpenServiceW", "StartServiceW", "CloseServiceHandle"],
    "SimpleOSSCM",
    "WineEventLog"
)
expect(wine_service_adapter_gate_with_service_result(adapter, service)).to_equal("ready")
```

</details>

#### keeps service readiness blocked on failed service-control evidence

- keeps service readiness blocked on failed service-control evidence
   - Expected: wine_service_adapter_gate_with_service_result(adapter, service) equals `service-control-empty-service`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps service readiness blocked on failed service-control evidence")
val adapter = wine_service_adapter_ready(_base_host_features())
val service = wine_advapi32_execute_service_start(
    ["OpenSCManagerW", "CreateServiceW", "OpenServiceW", "StartServiceW", "CloseServiceHandle"],
    "SimpleOSSCM",
    ""
)
expect(wine_service_adapter_gate_with_service_result(adapter, service)).to_equal("service-control-empty-service")
```

</details>

#### requires bounded audio device and buffer evidence before audio readiness

- requires bounded audio device and buffer evidence before audio readiness
   - Expected: wine_service_adapter_audio_gate(adapter, "waveOutOpen waveOutPrepareHeader waveOutClose audio-buffer-commit") equals `missing-peripheral-waveOutWrite`
   - Expected: wine_service_adapter_audio_gate(adapter, "waveOutOpen waveOutPrepareHeader waveOutWrite waveOutClose audio-buffer-commit") equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires bounded audio device and buffer evidence before audio readiness")
val adapter = wine_service_adapter_ready(_base_host_features())
expect(wine_service_adapter_audio_gate(adapter, "waveOutOpen waveOutPrepareHeader waveOutClose audio-buffer-commit")).to_equal("missing-peripheral-waveOutWrite")
expect(wine_service_adapter_audio_gate(adapter, "waveOutOpen waveOutPrepareHeader waveOutWrite waveOutClose audio-buffer-commit")).to_equal("ready")
```

</details>

#### requires font discovery and glyph raster evidence before font readiness

- requires font discovery and glyph raster evidence before font readiness
   - Expected: wine_service_adapter_font_gate(adapter, "EnumFontFamiliesExW CreateFontIndirectW font-raster-cache") equals `missing-peripheral-GetGlyphOutlineW`
   - Expected: wine_service_adapter_font_gate(adapter, "EnumFontFamiliesExW CreateFontIndirectW GetGlyphOutlineW font-raster-cache") equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires font discovery and glyph raster evidence before font readiness")
val adapter = wine_service_adapter_ready(_base_host_features())
expect(wine_service_adapter_font_gate(adapter, "EnumFontFamiliesExW CreateFontIndirectW font-raster-cache")).to_equal("missing-peripheral-GetGlyphOutlineW")
expect(wine_service_adapter_font_gate(adapter, "EnumFontFamiliesExW CreateFontIndirectW GetGlyphOutlineW font-raster-cache")).to_equal("ready")
```

</details>

#### requires keyboard, pointer, and message dispatch evidence before input readiness

- requires keyboard, pointer, and message dispatch evidence before input readiness
   - Expected: wine_service_adapter_input_gate(adapter, "GetKeyboardState GetCursorPos DispatchMessageW") equals `missing-peripheral-hid-event-queue`
   - Expected: wine_service_adapter_input_gate(adapter, "GetKeyboardState GetCursorPos DispatchMessageW hid-event-queue") equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires keyboard, pointer, and message dispatch evidence before input readiness")
val adapter = wine_service_adapter_ready(_base_host_features())
expect(wine_service_adapter_input_gate(adapter, "GetKeyboardState GetCursorPos DispatchMessageW")).to_equal("missing-peripheral-hid-event-queue")
expect(wine_service_adapter_input_gate(adapter, "GetKeyboardState GetCursorPos DispatchMessageW hid-event-queue")).to_equal("ready")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_service_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine host service adapter.
- Wine host service adapter

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f58dfde7860c82c6ff5151bfb13aa31e1fcf5580d265443bd91d76333ffe3cca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f58dfde7860c82c6ff5151bfb13aa31e1fcf5580d265443bd91d76333ffe3cca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f58dfde7860c82c6ff5151bfb13aa31e1fcf5580d265443bd91d76333ffe3cca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/wine_service_adapter_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_service_adapter_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_service_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_service_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_service_adapter_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists IPC, handle, audio, font, crypto, HID, printing, and multimedia services' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_service_adapter_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the first missing service' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_service_adapter_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unknown service declarations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
