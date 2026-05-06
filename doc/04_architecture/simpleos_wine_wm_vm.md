<!-- codex-design -->

# Architecture: SimpleOS Wine WM And VM Prerequisites

Date: 2026-05-06

## Decision

Separate Wine readiness into two explicit evidence lanes:

1. a Wine-facing X11/window adapter that binds to real SimpleOS window records and framebuffer presents;
2. a Wine-facing VM adapter that binds PE image mapping to an OS process id, address-space id, container evidence, stack/guard allocation, and no-host-code-jump policy.

Modeled compatibility gates remain valid for early diagnostics, but production readiness must call the stricter production gates.

## WM / Graphics Boundary

`src/lib/common/ui/wine_x11_adapter.spl` remains the Wine-facing X11-class contract. It is production-ready only after `wine_x11_backend_bind_simpleos` attaches evidence from `src/lib/common/ui/wine_simpleos_window_bridge.spl`.

The bridge writes SimpleOS `/win` records through `WindowRecord`, `WindowState`, `Rect`, and `BufferRef`, then records create, map, configure, focus, present, cursor, clipboard, and destroy evidence. Framebuffer presents produce deterministic checksum evidence so tests can distinguish a real SimpleOS window-record path from a modeled X11 string.

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

## Current Limits

This is not a complete upstream Wine port. The implemented contract proves auditable SimpleOS-backed WM and VM prerequisite surfaces for controlled fixtures. General Wine GUI drivers, arbitrary PE execution, broad NT/Win32 dispatch, kernel page-table enforcement, and full compositor event loops still require later implementation.
