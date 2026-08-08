# Proton Session Specification

> <details>

<!-- sdn-diagram:id=proton_session_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=proton_session_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

proton_session_spec -> common
proton_session_spec -> nogc_async_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=proton_session_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Proton Session Specification

## Scenarios

### Non-Wine Proton session planning

#### rejects incomplete session requests before runtime evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_app = proton_session_request_new("", "steamapps/compatdata/480/pfx", "hl2.exe", [])
expect(proton_session_request_gate(missing_app)).to_equal("missing-app-id")

val missing_prefix = proton_session_request_new("480", "", "hl2.exe", [])
expect(proton_session_request_gate(missing_prefix)).to_equal("missing-compat-prefix")

val invalid_prefix = proton_session_request_new("480", "tmp/pfx", "hl2.exe", [])
expect(proton_session_request_gate(invalid_prefix)).to_equal("invalid-compat-prefix")

val unsupported = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "README.txt", [])
expect(proton_session_request_gate(unsupported)).to_equal("unsupported-executable")
```

</details>

#### blocks session planning on incomplete non-Wine runtime evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid"])
val evidence = proton_non_wine_runtime_evidence_new(
    "steam-runtime abi-x86_64 soldier",
    "pressure-vessel-container container-rootfs container-rootfs-nvfs namespace-pid namespace-fs namespace-ipc namespace-net namespace-capability",
    "vulkan-loader vulkan-device dxvk",
    "proton-launcher steamworks-bridge controller-input",
    "esync-or-fsync"
)
val plan = proton_session_plan(request, evidence)
expect(plan.ok).to_equal(false)
expect(plan.error).to_equal("missing-vkd3d-proton")
expect(plan.status).to_equal("blocked")
```

</details>

#### plans a launch session when every non-Wine Proton subsystem is ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid", "-fullscreen"])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
expect(plan.ok).to_equal(true)
expect(plan.error).to_equal("")
expect(plan.app_id).to_equal("480")
expect(plan.compat_prefix).to_equal("steamapps/compatdata/480/pfx")
expect(plan.launch_command).to_equal("hl2.exe -novid -fullscreen")
expect(plan.runtime_features).to_contain("steam-runtime")
expect(plan.runtime_features).to_contain("pressure-vessel-container")
expect(plan.runtime_features).to_contain("dxvk")
expect(plan.runtime_features).to_contain("vkd3d-proton")
expect(plan.runtime_features).to_contain("esync-or-fsync")
expect(plan.status).to_equal("planned")
```

</details>

#### creates a dry-run handoff record without executing Proton

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid"])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
val exec_handoff = proton_session_launch_handoff(plan, false)
expect(exec_handoff.ok).to_equal(true)
expect(exec_handoff.status).to_equal("exec-dispatched")
expect(exec_handoff.launch_command).to_contain("wine64")

val handoff = proton_session_launch_handoff(plan, true)
expect(handoff.ok).to_equal(true)
expect(handoff.app_id).to_equal("480")
expect(handoff.compat_prefix).to_equal("steamapps/compatdata/480/pfx")
expect(handoff.launch_command).to_equal("hl2.exe -novid")
expect(handoff.container_profile).to_contain("pressure-vessel")
expect(handoff.container_profile).to_contain("container-rootfs-nvfs")
expect(handoff.container_profile).to_contain("namespace-capability")
expect(handoff.runtime_features).to_contain("steam-runtime")
expect(handoff.runtime_features).to_contain("vkd3d-proton")
expect(handoff.status).to_equal("dry-run-ready")
```

</details>

#### requires SimpleOS MDSOC executable-environment evidence before dry-run handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid"])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
val missing_exec_env = proton_session_launch_handoff_with_exec_env(plan, true, "simpleos-qemu-vm")
expect(missing_exec_env.ok).to_equal(false)
expect(missing_exec_env.error).to_equal("exec-env:missing-simpleos-full-os-boot")

val handoff = proton_session_launch_handoff_with_exec_env(plan, true, wine_simpleos_exec_env_fixture_evidence())
expect(handoff.ok).to_equal(true)
expect(handoff.status).to_equal("dry-run-ready")
expect(handoff.container_profile).to_contain("pressure-vessel")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/proton_session_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Non-Wine Proton session planning

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
