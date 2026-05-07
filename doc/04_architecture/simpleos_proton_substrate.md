<!-- codex-architecture -->

# Architecture: SimpleOS Proton Substrate

Date: 2026-05-07

## Decision

Treat Proton as a higher readiness layer above the full SimpleOS Wine substrate,
not as a synonym for the controlled Wine hello milestones.

The Proton gate requires:

1. `wine_substrate_full_wine_gate(...) == "ready"`;
2. Steam runtime and pressure-vessel style container evidence;
3. Proton launcher evidence;
4. Vulkan loader and Vulkan device evidence;
5. DXVK and VKD3D-Proton graphics translation evidence;
6. Steamworks bridge evidence;
7. controller/input, shader cache, and esync-or-fsync evidence.

## MDSOC+ Placement

The Proton layer follows the same MDSOC+ split as the Wine layer:

- `src/lib/common/wine_proton_gate.spl` is a common tree-node facade. It owns
  readiness vocabulary only, not runtime state.
- `src/lib/common/proton_runtime_subsystems.spl` is the common non-Wine
  subsystem facade. It owns Steam runtime ABI, pressure-vessel container,
  graphics translation, Steam integration, shader-cache, and sync evidence
  gates without depending on Wine internals.
- `src/lib/common/proton_session.spl` is the common launch-session planner for
  non-Wine state. It validates app/prefix/executable records and composes
  non-Wine subsystem evidence into a planned launch record without executing
  Wine or game code.
- A future Steam/Proton userland service is an MDSOC+ capsule: MDSOC
  ports/capabilities outside, ECS world inside for app id, prefix, container,
  runtime, shader-cache, controller, and launch-session records.
- Kernel VM, scheduler, device, and Vulkan driver state remain MDSOC-only.
- Proton adapters must translate to native SimpleOS process, container,
  filesystem, graphics, input, and Steamworks bridge ports. They must not bypass
  those owners.

## Boundary

This is a readiness classifier. It does not implement upstream Proton, Steam
client integration, a Linux ABI, a Vulkan driver, DXVK, VKD3D-Proton, or
arbitrary Windows game compatibility.

## References

- Valve Proton README: `https://github.com/ValveSoftware/Proton`
- Valve Proton requirements wiki: `https://github.com/ValveSoftware/Proton/wiki/Requirements`
