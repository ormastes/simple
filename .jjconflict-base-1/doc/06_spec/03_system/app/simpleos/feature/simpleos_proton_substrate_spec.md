# Simpleos Proton Substrate Specification

> 1. wine proton fixture features

<!-- sdn-diagram:id=simpleos_proton_substrate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_proton_substrate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_proton_substrate_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_proton_substrate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Proton Substrate Specification

## Scenarios

### SimpleOS Proton Substrate

### REQ-PROTON-001: full Wine dependency

#### should block Proton readiness until full Wine readiness is complete

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

### REQ-PROTON-002: Steam runtime and container

#### should require the Proton launcher, Steam runtime, and pressure-vessel style container evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_proton_feature_gate("")).to_equal("missing-steam-runtime")
expect(wine_proton_feature_gate("steam-runtime")).to_equal("missing-pressure-vessel-container")
expect(wine_proton_feature_gate("steam-runtime pressure-vessel-container")).to_equal("missing-proton-launcher")
```

</details>

### REQ-PROTON-003: graphics translation

#### should require Vulkan, DXVK, and VKD3D-Proton evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = "steam-runtime pressure-vessel-container proton-launcher wine-full"
expect(wine_proton_feature_gate(features)).to_equal("missing-vulkan-loader")
expect(wine_proton_feature_gate(features + " vulkan-loader vulkan-device")).to_equal("missing-dxvk")
expect(wine_proton_feature_gate(features + " vulkan-loader vulkan-device dxvk")).to_equal("missing-vkd3d-proton")
```

</details>

### REQ-PROTON-004: Steam/game runtime integration

#### should require Steamworks, controller input, shader cache, and sync primitive evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = "steam-runtime pressure-vessel-container proton-launcher wine-full " +
    "vulkan-loader vulkan-device dxvk vkd3d-proton"
expect(wine_proton_feature_gate(features)).to_equal("missing-steamworks-bridge")
expect(wine_proton_feature_gate(features + " steamworks-bridge")).to_equal("missing-controller-input")
expect(wine_proton_feature_gate(features + " steamworks-bridge controller-input")).to_equal("missing-shader-cache")
expect(wine_proton_feature_gate(features + " steamworks-bridge controller-input shader-cache")).to_equal("missing-esync-or-fsync")
```

</details>

### REQ-PROTON-005: readiness boundary

#### should mark Proton ready only when full Wine and all Proton features are present

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_proton_readiness_gate(wine_proton_fixture_wine_gates(), wine_proton_fixture_features())).to_equal("ready")
```

</details>

### REQ-PROTON-006: structured runtime evidence

#### should require structured Steam runtime, pressure-vessel, graphics, integration, and sync evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_proton_runtime_gate(wine_proton_fixture_runtime_evidence())).to_equal("ready")
expect(wine_proton_runtime_readiness_gate(wine_proton_fixture_wine_gates(), wine_proton_fixture_runtime_evidence())).to_equal("ready")
```

</details>

### REQ-PROTON-007: non-Wine Proton subsystem evidence

#### should complete every Proton prerequisite outside Wine itself

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = proton_fixture_non_wine_runtime_evidence()
expect(proton_non_wine_runtime_gate(evidence)).to_equal("ready")
expect(proton_non_wine_feature_evidence(evidence)).to_contain("steam-runtime")
expect(proton_non_wine_feature_evidence(evidence)).to_contain("pressure-vessel-container")
expect(proton_non_wine_feature_evidence(evidence)).to_contain("dxvk")
expect(proton_non_wine_feature_evidence(evidence)).to_contain("vkd3d-proton")
expect(proton_non_wine_feature_evidence(evidence)).to_contain("steamworks-bridge")
expect(proton_non_wine_feature_evidence(evidence)).to_contain("esync-or-fsync")
```

</details>

### REQ-PROTON-008: non-Wine launch session planning

#### should plan a Proton session after non-Wine subsystem evidence is complete

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid"])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
expect(plan.ok).to_equal(true)
expect(plan.status).to_equal("planned")
expect(plan.launch_command).to_equal("hl2.exe -novid")
expect(plan.runtime_features).to_contain("pressure-vessel-container")
expect(plan.runtime_features).to_contain("vkd3d-proton")
```

</details>

### REQ-PROTON-009: non-executing launch handoff

#### should emit a dry-run handoff and keep real execution blocked

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid"])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
expect(proton_session_launch_handoff(plan, false).error).to_equal("execution-not-implemented")
val handoff = proton_session_launch_handoff(plan, true)
expect(handoff.status).to_equal("dry-run-ready")
expect(handoff.container_profile).to_contain("pressure-vessel")
expect(handoff.container_profile).to_contain("container-rootfs-nvfs")
expect(handoff.container_profile).to_contain("namespace-capability")
expect(handoff.runtime_features).to_contain("dxvk")
```

</details>

#### should require SimpleOS MDSOC executable-environment evidence before Proton dry-run handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid"])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
val blocked = proton_session_launch_handoff_with_exec_env(plan, true, "simpleos-qemu-vm")
expect(blocked.error).to_equal("exec-env:missing-simpleos-full-os-boot")
val handoff = proton_session_launch_handoff_with_exec_env(plan, true, wine_simpleos_exec_env_fixture_evidence())
expect(handoff.status).to_equal("dry-run-ready")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_proton_substrate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Proton Substrate
- REQ-PROTON-001: full Wine dependency
- REQ-PROTON-002: Steam runtime and container
- REQ-PROTON-003: graphics translation
- REQ-PROTON-004: Steam/game runtime integration
- REQ-PROTON-005: readiness boundary
- REQ-PROTON-006: structured runtime evidence
- REQ-PROTON-007: non-Wine Proton subsystem evidence
- REQ-PROTON-008: non-Wine launch session planning
- REQ-PROTON-009: non-executing launch handoff

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
