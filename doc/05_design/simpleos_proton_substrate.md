<!-- codex-design -->

# Detail Design: SimpleOS Proton Substrate

Date: 2026-05-07

## Gate

`src/lib/common/wine_proton_gate.spl` exposes:

- `wine_proton_required_features()`;
- `wine_proton_missing_features(features)`;
- `wine_proton_feature_gate(features)`;
- `wine_proton_readiness_gate(wine_gates, proton_features)`.

The readiness gate first calls `wine_substrate_full_wine_gate(wine_gates)`.
Only a full Wine-ready substrate can advance to Proton-specific checks.

`src/lib/common/proton_runtime_subsystems.spl` exposes the non-Wine Proton
subsystem gates:

- `proton_steam_runtime_gate(evidence)`;
- `proton_pressure_vessel_gate(evidence)`;
- `proton_graphics_translation_gate(evidence)`;
- `proton_steam_integration_gate(evidence)`;
- `proton_sync_gate(evidence)`;
- `proton_non_wine_runtime_gate(evidence)`;
- `proton_non_wine_feature_evidence(evidence)`.

`wine_proton_runtime_gate` composes these subsystem gates and adds only the
outer full-Wine dependency plus `wine-full` feature evidence.

`src/lib/common/proton_session.spl` exposes non-Wine launch-session planning:

- `proton_session_request_new(app_id, compat_prefix, executable_path, args)`;
- `proton_session_request_gate(request)`;
- `proton_session_plan(request, evidence)`.

The session planner validates Steam app id, compat prefix, executable path, and
non-Wine runtime subsystem evidence. It emits a planned launch command and
runtime feature evidence, but does not execute Wine or a game process.

`src/app/proton_session_plan/main.spl` is a narrow command surface for this
planner. It prints app id, compat prefix, planned command, status, and runtime
features for the fixture non-Wine Proton evidence.

## Required Proton Features

- `steam-runtime`
- `pressure-vessel-container`
- `proton-launcher`
- `wine-full`
- `vulkan-loader`
- `vulkan-device`
- `dxvk`
- `vkd3d-proton`
- `steamworks-bridge`
- `controller-input`
- `shader-cache`
- `esync-or-fsync`

## MDSOC+ Service Shape

A future resident Proton service must define:

- World: `ProtonSessionWorld`
- Components: `SteamAppId`, `CompatPrefix`, `RuntimeBinding`,
  `ContainerBinding`, `VulkanDeviceBinding`, `DxvkBinding`,
  `Vkd3dBinding`, `SteamworksBridge`, `ControllerRoute`,
  `ShaderCacheEntry`, `SyncPrimitiveMode`, `LaunchStatus`
- Systems: `sys_prepare_prefix`, `sys_bind_runtime`, `sys_enter_container`,
  `sys_bind_graphics_translation`, `sys_bind_steamworks`,
  `sys_route_controller_input`, `sys_prepare_shader_cache`,
  `sys_launch_game`, `sys_collect_exit_status`

This keeps Proton state in an ECS world inside the owning MDSOC+ userland
capsule, while the common gate remains stateless.
