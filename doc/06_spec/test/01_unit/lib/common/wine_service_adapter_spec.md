# Wine Service Adapter Specification

> <details>

<!-- sdn-diagram:id=wine_service_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_service_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_service_adapter_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_service_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Service Adapter Specification

## Scenarios

### Wine host service adapter

#### lists IPC, handle, audio, font, crypto, HID, printing, and multimedia services

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = wine_service_adapter_required_services()
expect(services.len()).to_be_greater_than(10)
expect(services[0]).to_equal("ipc-server")
```

</details>

#### reports the first missing service

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing = wine_service_adapter_missing_services("ipc-server handle-table")
expect(missing[0]).to_equal("audio-device")
```

</details>

#### rejects unknown service declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_service_adapter_add(wine_service_adapter_new(_base_host_features()), "unknown")
expect(result.ok).to_equal(false)
expect(result.state).to_equal("unknown-service")
```

</details>

#### derives host features only from complete service pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = wine_service_adapter_new(_base_host_features())
val added = wine_service_adapter_add(adapter, "ipc-server")
expect(wine_service_adapter_gate(added.adapter)).to_equal("missing-service-handle-table")
```

</details>

#### reaches the existing host gate when all service and base features are present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = wine_service_adapter_ready(_base_host_features())
expect(wine_service_adapter_gate(adapter)).to_equal("ready")
```

</details>

#### requires bounded ADVAPI32 service-control evidence before service readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = wine_service_adapter_ready(_base_host_features())
expect(wine_service_adapter_audio_gate(adapter, "waveOutOpen waveOutPrepareHeader waveOutClose audio-buffer-commit")).to_equal("missing-peripheral-waveOutWrite")
expect(wine_service_adapter_audio_gate(adapter, "waveOutOpen waveOutPrepareHeader waveOutWrite waveOutClose audio-buffer-commit")).to_equal("ready")
```

</details>

#### requires font discovery and glyph raster evidence before font readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = wine_service_adapter_ready(_base_host_features())
expect(wine_service_adapter_font_gate(adapter, "EnumFontFamiliesExW CreateFontIndirectW font-raster-cache")).to_equal("missing-peripheral-GetGlyphOutlineW")
expect(wine_service_adapter_font_gate(adapter, "EnumFontFamiliesExW CreateFontIndirectW GetGlyphOutlineW font-raster-cache")).to_equal("ready")
```

</details>

#### requires keyboard, pointer, and message dispatch evidence before input readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/lib/common/wine_service_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
