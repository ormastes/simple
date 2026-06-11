# Wine Proton Runtime Specification

> <details>

<!-- sdn-diagram:id=wine_proton_runtime_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_proton_runtime_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_proton_runtime_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_proton_runtime_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Proton Runtime Specification

## Scenarios

### Wine Proton runtime evidence

#### requires Steam runtime ABI evidence before Proton can launch

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_runtime = wine_proton_runtime_evidence_new("", "", "", "", "")
expect(wine_proton_runtime_gate(missing_runtime)).to_equal("missing-steam-runtime")

val missing_abi = wine_proton_runtime_evidence_new("steam-runtime soldier", "", "", "", "")
expect(wine_proton_runtime_gate(missing_abi)).to_equal("missing-abi-x86_64")

val missing_generation = wine_proton_runtime_evidence_new("steam-runtime abi-x86_64", "", "", "", "")
expect(wine_proton_runtime_gate(missing_generation)).to_equal("missing-steam-linux-runtime-generation")
```

</details>

#### requires pressure-vessel style container rootfs and namespaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_rootfs = wine_proton_runtime_evidence_new("steam-runtime abi-x86_64 soldier", "pressure-vessel-container namespace-pid namespace-fs namespace-ipc namespace-net namespace-capability", "", "", "")
expect(wine_proton_runtime_gate(missing_rootfs)).to_equal("missing-container-rootfs")

val missing_backend = wine_proton_runtime_evidence_new("steam-runtime abi-x86_64 soldier", "pressure-vessel-container container-rootfs namespace-pid namespace-fs namespace-ipc namespace-net namespace-capability", "", "", "")
expect(wine_proton_runtime_gate(missing_backend)).to_equal("missing-container-rootfs-nvfs")

val missing_namespace = wine_proton_runtime_evidence_new("steam-runtime abi-x86_64 soldier", "pressure-vessel-container container-rootfs container-rootfs-nvfs namespace-pid namespace-fs namespace-ipc namespace-net", "", "", "")
expect(wine_proton_runtime_gate(missing_namespace)).to_equal("missing-namespace-capability")
```

</details>

#### requires Vulkan, DXVK, VKD3D-Proton, shader cache, and Steam integration

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_dxvk = wine_proton_runtime_evidence_new(
    "steam-runtime abi-x86_64 soldier",
    "pressure-vessel-container container-rootfs container-rootfs-nvfs namespace-pid namespace-fs namespace-ipc namespace-net namespace-capability",
    "vulkan-loader vulkan-device",
    "proton-launcher steamworks-bridge controller-input",
    "esync-or-fsync"
)
expect(wine_proton_runtime_gate(missing_dxvk)).to_equal("missing-dxvk")

val missing_steamworks = wine_proton_runtime_evidence_new(
    "steam-runtime abi-x86_64 soldier",
    "pressure-vessel-container container-rootfs container-rootfs-nvfs namespace-pid namespace-fs namespace-ipc namespace-net namespace-capability",
    "vulkan-loader vulkan-device dxvk vkd3d-proton shader-cache",
    "proton-launcher controller-input",
    "esync-or-fsync"
)
expect(wine_proton_runtime_gate(missing_steamworks)).to_equal("missing-steamworks-bridge")
```

</details>

#### derives the legacy Proton feature string from structured evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = wine_proton_runtime_feature_evidence(wine_proton_fixture_runtime_evidence())
expect(features).to_contain("steam-runtime")
expect(features).to_contain("pressure-vessel-container")
expect(features).to_contain("wine-full")
expect(features).to_contain("vulkan-device")
expect(features).to_contain("dxvk")
expect(features).to_contain("vkd3d-proton")
expect(features).to_contain("esync-or-fsync")
```

</details>

#### keeps structured Proton runtime readiness blocked on incomplete Wine

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_proton_runtime_readiness_gate("process=verified exec_env=verified", wine_proton_fixture_runtime_evidence())
expect(state).to_equal("blocked-wine-blocked-missing-vm")
```

</details>

#### allows structured Proton readiness only when Wine and runtime evidence are complete

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_proton_runtime_readiness_gate(wine_proton_fixture_wine_gates(), wine_proton_fixture_runtime_evidence())
expect(state).to_equal("ready")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_proton_runtime_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine Proton runtime evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
