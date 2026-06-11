# Wine Proton Gate Specification

> <details>

<!-- sdn-diagram:id=wine_proton_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_proton_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_proton_gate_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_proton_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Proton Gate Specification

## Scenarios

### Wine Proton readiness gate

#### lists Proton-specific runtime prerequisites above Wine

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val required = wine_proton_required_features()
expect(required.len()).to_equal(12)
expect(required[0]).to_equal("steam-runtime")
expect(required[1]).to_equal("pressure-vessel-container")
expect(required[5]).to_equal("vulkan-device")
expect(required[6]).to_equal("dxvk")
expect(required[7]).to_equal("vkd3d-proton")
expect(required[11]).to_equal("esync-or-fsync")
```

</details>

#### reports the first missing Proton feature

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_proton_feature_gate("steam-runtime pressure-vessel-container")
expect(state).to_equal("missing-proton-launcher")
val missing = wine_proton_missing_features("steam-runtime pressure-vessel-container")
expect(missing.len()).to_equal(10)
expect(missing[0]).to_equal("proton-launcher")
```

</details>

#### keeps Proton blocked until full Wine readiness is verified

1. wine proton fixture features
   - Expected: state equals `blocked-wine-blocked-missing-user32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_proton_readiness_gate(
    "process=verified exec_env=verified vm=verified renderer=verified",
    wine_proton_fixture_features()
)
expect(state).to_equal("blocked-wine-blocked-missing-user32")
```

</details>

#### keeps Proton blocked on missing graphics translation features

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = "steam-runtime pressure-vessel-container proton-launcher wine-full " +
    "vulkan-loader vulkan-device dxvk steamworks-bridge controller-input shader-cache esync-or-fsync"
val state = wine_proton_readiness_gate(wine_proton_fixture_wine_gates(), features)
expect(state).to_equal("missing-vkd3d-proton")
```

</details>

#### allows Proton readiness only when Wine and Proton gates are complete

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_proton_readiness_gate(wine_proton_fixture_wine_gates(), wine_proton_fixture_features())
expect(state).to_equal("ready")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_proton_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine Proton readiness gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
