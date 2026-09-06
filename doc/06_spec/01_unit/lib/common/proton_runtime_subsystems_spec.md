# Proton Runtime Subsystems Specification

> Tests covering Non-Wine Proton runtime subsystems.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Proton Runtime Subsystems Specification

## Scenarios

### Non-Wine Proton runtime subsystems

#### gates Steam runtime ABI without depending on Wine

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- gates Steam runtime ABI without depending on Wine
   - Expected: proton_steam_runtime_gate("") equals `missing-steam-runtime`
   - Expected: proton_steam_runtime_gate("steam-runtime soldier") equals `missing-abi-x86_64`
   - Expected: proton_steam_runtime_gate("steam-runtime abi-x86_64") equals `missing-steam-linux-runtime-generation`
   - Expected: proton_steam_runtime_gate("steam-runtime abi-x86_64 soldier") equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gates Steam runtime ABI without depending on Wine")
expect(proton_steam_runtime_gate("")).to_equal("missing-steam-runtime")
expect(proton_steam_runtime_gate("steam-runtime soldier")).to_equal("missing-abi-x86_64")
expect(proton_steam_runtime_gate("steam-runtime abi-x86_64")).to_equal("missing-steam-linux-runtime-generation")
expect(proton_steam_runtime_gate("steam-runtime abi-x86_64 soldier")).to_equal("ready")
```

</details>

#### gates pressure-vessel container evidence without depending on Wine

- gates pressure-vessel container evidence without depending on Wine
   - Expected: proton_pressure_vessel_gate("pressure-vessel-container namespace-pid namespace-fs namespace-ipc namespace-net namespace-capability") equals `missing-container-rootfs`
   - Expected: proton_pressure_vessel_gate("pressure-vessel-container container-rootfs namespace-pid namespace-fs namespace-ipc namespace-net namespace-capability") equals `missing-container-rootfs-nvfs`
   - Expected: proton_pressure_vessel_gate("pressure-vessel-container container-rootfs container-rootfs-nvfs namespace-pid namespace-fs namespace-ipc namespace-net") equals `missing-namespace-capability`
   - Expected: proton_pressure_vessel_gate("pressure-vessel-container container-rootfs container-rootfs-nvfs namespace-pid namespace-fs namespace-ipc namespace-net namespace-capability") equals `ready`
   - Expected: proton_pressure_vessel_gate("pressure-vessel-container container-rootfs container-rootfs-nvfs stupid namespace-fs namespace-ipc namespace-net namespace-capability") equals `missing-namespace-pid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gates pressure-vessel container evidence without depending on Wine")
expect(proton_pressure_vessel_gate("pressure-vessel-container namespace-pid namespace-fs namespace-ipc namespace-net namespace-capability")).to_equal("missing-container-rootfs")
expect(proton_pressure_vessel_gate("pressure-vessel-container container-rootfs namespace-pid namespace-fs namespace-ipc namespace-net namespace-capability")).to_equal("missing-container-rootfs-nvfs")
expect(proton_pressure_vessel_gate("pressure-vessel-container container-rootfs container-rootfs-nvfs namespace-pid namespace-fs namespace-ipc namespace-net")).to_equal("missing-namespace-capability")
expect(proton_pressure_vessel_gate("pressure-vessel-container container-rootfs container-rootfs-nvfs namespace-pid namespace-fs namespace-ipc namespace-net namespace-capability")).to_equal("ready")
expect(proton_pressure_vessel_gate("pressure-vessel-container container-rootfs container-rootfs-nvfs stupid namespace-fs namespace-ipc namespace-net namespace-capability")).to_equal("missing-namespace-pid")
```

</details>

#### gates Vulkan graphics translation evidence without depending on Wine

- gates Vulkan graphics translation evidence without depending on Wine
   - Expected: proton_graphics_translation_gate("vulkan-loader vulkan-device") equals `missing-dxvk`
   - Expected: proton_graphics_translation_gate("vulkan-loader vulkan-device dxvk") equals `missing-vkd3d-proton`
   - Expected: proton_graphics_translation_gate("vulkan-loader vulkan-device dxvk vkd3d-proton") equals `missing-shader-cache`
   - Expected: proton_graphics_translation_gate("vulkan-loader vulkan-device dxvk vkd3d-proton shader-cache") equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gates Vulkan graphics translation evidence without depending on Wine")
expect(proton_graphics_translation_gate("vulkan-loader vulkan-device")).to_equal("missing-dxvk")
expect(proton_graphics_translation_gate("vulkan-loader vulkan-device dxvk")).to_equal("missing-vkd3d-proton")
expect(proton_graphics_translation_gate("vulkan-loader vulkan-device dxvk vkd3d-proton")).to_equal("missing-shader-cache")
expect(proton_graphics_translation_gate("vulkan-loader vulkan-device dxvk vkd3d-proton shader-cache")).to_equal("ready")
```

</details>

#### gates Steam integration and sync evidence without depending on Wine

- gates Steam integration and sync evidence without depending on Wine
   - Expected: proton_steam_integration_gate("proton-launcher controller-input") equals `missing-steamworks-bridge`
   - Expected: proton_steam_integration_gate("proton-launcher steamworks-bridge controller-input") equals `ready`
   - Expected: proton_sync_gate("") equals `missing-esync-or-fsync`
   - Expected: proton_sync_gate("esync-or-fsync") equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gates Steam integration and sync evidence without depending on Wine")
expect(proton_steam_integration_gate("proton-launcher controller-input")).to_equal("missing-steamworks-bridge")
expect(proton_steam_integration_gate("proton-launcher steamworks-bridge controller-input")).to_equal("ready")
expect(proton_sync_gate("")).to_equal("missing-esync-or-fsync")
expect(proton_sync_gate("esync-or-fsync")).to_equal("ready")
```

</details>

#### composes every non-Wine Proton subsystem

- composes every non-Wine Proton subsystem
   - Expected: proton_non_wine_runtime_gate(missing) equals `missing-vkd3d-proton`
   - Expected: proton_non_wine_runtime_gate(proton_fixture_non_wine_runtime_evidence()) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("composes every non-Wine Proton subsystem")
val missing = proton_non_wine_runtime_evidence_new(
    "steam-runtime abi-x86_64 soldier",
    "pressure-vessel-container container-rootfs container-rootfs-nvfs namespace-pid namespace-fs namespace-ipc namespace-net namespace-capability",
    "vulkan-loader vulkan-device dxvk",
    "proton-launcher steamworks-bridge controller-input",
    "esync-or-fsync"
)
expect(proton_non_wine_runtime_gate(missing)).to_equal("missing-vkd3d-proton")
expect(proton_non_wine_runtime_gate(proton_fixture_non_wine_runtime_evidence())).to_equal("ready")
```

</details>

#### derives Proton feature evidence for the higher readiness gate

- derives Proton feature evidence for the higher readiness gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("derives Proton feature evidence for the higher readiness gate")
val features = proton_non_wine_feature_evidence(proton_fixture_non_wine_runtime_evidence())
expect(features).to_contain("steam-runtime")
expect(features).to_contain("pressure-vessel-container")
expect(features).to_contain("vulkan-loader")
expect(features).to_contain("dxvk")
expect(features).to_contain("vkd3d-proton")
expect(features).to_contain("steamworks-bridge")
expect(features).to_contain("controller-input")
expect(features).to_contain("shader-cache")
expect(features).to_contain("esync-or-fsync")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/proton_runtime_subsystems_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Non-Wine Proton runtime subsystems.
- Non-Wine Proton runtime subsystems

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `7602c60e8e69532c80d8b7098f1b876456cfe34ed16c13cb66ce8e6d3a863252`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7602c60e8e69532c80d8b7098f1b876456cfe34ed16c13cb66ce8e6d3a863252`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7602c60e8e69532c80d8b7098f1b876456cfe34ed16c13cb66ce8e6d3a863252`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/proton_runtime_subsystems_spec.spl
mirror: doc/06_spec/01_unit/lib/common/proton_runtime_subsystems_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/proton_runtime_subsystems_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/proton_runtime_subsystems_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/proton_runtime_subsystems_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gates Steam runtime ABI without depending on Wine' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/proton_runtime_subsystems_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gates pressure-vessel container evidence without depending on Wine' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/proton_runtime_subsystems_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gates Vulkan graphics translation evidence without depending on Wine' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
