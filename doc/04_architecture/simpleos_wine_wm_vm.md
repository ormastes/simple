<!-- codex-design -->

# Architecture: SimpleOS Wine WM And VM Prerequisites

Date: 2026-05-06

## Decision

Separate Wine readiness into two explicit MDSOC+ evidence lanes:

1. a Wine-facing X11/window adapter that binds to real SimpleOS window records and framebuffer presents;
2. a Wine-facing VM adapter that binds PE image mapping to an OS process id, address-space id, container evidence, stack/guard allocation, and no-host-code-jump policy.

Modeled compatibility gates remain valid for early diagnostics, but production readiness must call the stricter production gates.

## MDSOC+ Placement

The WM/VM prerequisite path is based on the same MDSOC+ split used by
SimpleOS userland:

- `src/lib/common/ui/wine_x11_adapter.spl` and
  `src/lib/common/ui/wine_simpleos_window_bridge.spl` are common tree-node
  facades. They describe the Wine-facing X11-class contract and evidence shape;
  they do not own the final compositor state.
- A resident SimpleOS WM service owns window/session state as an MDSOC+ userland
  capsule: MDSOC ports/capabilities outside, ECS `World` inside. Expected
  components are window record, surface/buffer ref, damage region, focus,
  cursor, clipboard, input event, and present checksum evidence.
- `src/lib/common/wine_vm_adapter.spl` and
  `src/lib/common/wine_image_vm_map.spl` are VM/PE mapping facades. The kernel
  page-table and fault machinery remains MDSOC-only; the userland process or
  container manager that tracks namespaces, process identities, and executable
  sessions is MDSOC+.
- Wine/Win32/X11-class adapters translate between Wine concepts and native
  SimpleOS ports. They must not bypass native WM, VM, process, filesystem,
  container, or capability ownership.

This keeps the architecture MDSOC+ based without moving ECS into kernel or
driver code.

## WM / Graphics Boundary

`src/lib/common/ui/wine_x11_adapter.spl` remains the Wine-facing X11-class contract. It is production-ready only after `wine_x11_backend_bind_simpleos` attaches evidence from `src/lib/common/ui/wine_simpleos_window_bridge.spl`.

The bridge writes SimpleOS `/win` records through `WindowRecord`, `WindowState`, `Rect`, and `BufferRef`, then records create, map, configure, focus, present, cursor, clipboard, and destroy evidence. Framebuffer presents produce deterministic checksum evidence so tests can distinguish a real SimpleOS window-record path from a modeled X11 string.

`src/lib/common/wine_gui_hello.spl` composes this boundary with the controlled PE hello path: the executable must first pass OS-backed VM image mapping and controlled NT stdout execution, then the GUI milestone creates Wine-facing X11 state and binds it to SimpleOS `/win` framebuffer evidence before reporting execution.

## VM / Container Boundary

`src/lib/common/wine_vm_adapter.spl` distinguishes modeled VM spaces from OS-backed VM process spaces. Production VM readiness requires:

- non-zero process id and address-space id;
- container evidence for pid, fs, ipc, net, and capability namespaces;
- OS-backed VMA regions;
- executable PE image mapping;
- thread stack plus guard page;
- fault-delivery evidence;
- no-host-code-jump policy.

`src/lib/common/wine_image_vm_map.spl` maps validated PE images into that process space before controlled hello execution can proceed.

## MDSOC+ Component Sketch

| Capsule | Components | Systems |
|---|---|---|
| WM service | `WindowRecord`, `SurfaceRef`, `DamageRegion`, `FocusState`, `CursorState`, `ClipboardValue`, `InputEvent`, `PresentEvidence` | create/map/configure/focus/present/destroy, input dispatch, clipboard update |
| Process/container service | `ProcessIdentity`, `AddressSpaceIdentity`, `NamespaceFacet`, `CapabilityBoundary`, `RootfsBinding`, `ExitStatus` | spawn, wait/reap, namespace bind, capability check, rootfs mount |
| VM/session service | `VmaRegion`, `ImageSection`, `StackRegion`, `GuardPage`, `FaultRecord`, `NoHostJumpPolicy` | reserve/map/protect/unmap, stack setup, fault classify, executable policy check |
| Wine service facade | `ImportBinding`, `NtHandle`, `RegistryKey`, `ServiceHandle`, `AudioBuffer`, `FontFace`, `InputMessage` | import bind, handle dispatch, registry roundtrip, service-control dispatch, peripheral evidence |

## Current Limits

This is not a complete upstream Wine port. The implemented contract proves auditable SimpleOS-backed WM and VM prerequisite surfaces for controlled fixtures, including a controlled GUI hello milestone. General Wine GUI drivers, arbitrary PE execution, broad NT/Win32 dispatch, kernel page-table enforcement, and full compositor event loops still require later implementation.
