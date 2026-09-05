# Proton Runtime Subsystems Specification

> <details>

<!-- sdn-diagram:id=proton_runtime_subsystems_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=proton_runtime_subsystems_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

proton_runtime_subsystems_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=proton_runtime_subsystems_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Proton Runtime Subsystems Specification

## Scenarios

### Non-Wine Proton runtime subsystems

#### gates Steam runtime ABI without depending on Wine

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(proton_steam_runtime_gate("")).to_equal("missing-steam-runtime")
expect(proton_steam_runtime_gate("steam-runtime soldier")).to_equal("missing-abi-x86_64")
expect(proton_steam_runtime_gate("steam-runtime abi-x86_64")).to_equal("missing-steam-linux-runtime-generation")
expect(proton_steam_runtime_gate("steam-runtime abi-x86_64 soldier")).to_equal("ready")
```

</details>

#### gates pressure-vessel container evidence without depending on Wine

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(proton_pressure_vessel_gate("pressure-vessel-container namespace-pid namespace-fs namespace-ipc namespace-net namespace-capability")).to_equal("missing-container-rootfs")
expect(proton_pressure_vessel_gate("pressure-vessel-container container-rootfs namespace-pid namespace-fs namespace-ipc namespace-net namespace-capability")).to_equal("missing-container-rootfs-nvfs")
expect(proton_pressure_vessel_gate("pressure-vessel-container container-rootfs container-rootfs-nvfs namespace-pid namespace-fs namespace-ipc namespace-net")).to_equal("missing-namespace-capability")
expect(proton_pressure_vessel_gate("pressure-vessel-container container-rootfs container-rootfs-nvfs namespace-pid namespace-fs namespace-ipc namespace-net namespace-capability")).to_equal("ready")
expect(proton_pressure_vessel_gate("pressure-vessel-container container-rootfs container-rootfs-nvfs stupid namespace-fs namespace-ipc namespace-net namespace-capability")).to_equal("missing-namespace-pid")
```

</details>

#### gates Vulkan graphics translation evidence without depending on Wine

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(proton_graphics_translation_gate("vulkan-loader vulkan-device")).to_equal("missing-dxvk")
expect(proton_graphics_translation_gate("vulkan-loader vulkan-device dxvk")).to_equal("missing-vkd3d-proton")
expect(proton_graphics_translation_gate("vulkan-loader vulkan-device dxvk vkd3d-proton")).to_equal("missing-shader-cache")
expect(proton_graphics_translation_gate("vulkan-loader vulkan-device dxvk vkd3d-proton shader-cache")).to_equal("ready")
```

</details>

#### gates Steam integration and sync evidence without depending on Wine

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(proton_steam_integration_gate("proton-launcher controller-input")).to_equal("missing-steamworks-bridge")
expect(proton_steam_integration_gate("proton-launcher steamworks-bridge controller-input")).to_equal("ready")
expect(proton_sync_gate("")).to_equal("missing-esync-or-fsync")
expect(proton_sync_gate("esync-or-fsync")).to_equal("ready")
```

</details>

#### composes every non-Wine Proton subsystem

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
