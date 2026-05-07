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
