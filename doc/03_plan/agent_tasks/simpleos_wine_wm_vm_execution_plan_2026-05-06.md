# SimpleOS Wine WM And VM Execution Plan

Date: 2026-05-06

## Target

Replace modeled readiness for the remaining Wine prerequisites with auditable SimpleOS-backed gates:

- Wine-compatible WM / graphics substrate.
- Wine-compatible process container / VM memory substrate with OS-backed process identity.

## Acceptance Criteria

1. WM production readiness requires SimpleOS window records and framebuffer present evidence.
2. VM production readiness requires process id, address-space id, container namespace evidence, OS VMA image mapping, stack/guard setup, fault evidence, and no-host-code-jump policy.
3. The controlled `hello.exe` path maps its PE image into the VM process before execution.
4. Tests distinguish modeled readiness from production evidence.
5. The audit names residual blockers instead of claiming a full Wine port.

## Result

Implemented in `src/lib/common/ui/wine_simpleos_window_bridge.spl`, `src/lib/common/ui/wine_x11_adapter.spl`, `src/lib/common/wine_vm_adapter.spl`, `src/lib/common/wine_image_vm_map.spl`, and `src/lib/common/wine_hello_exe.spl`.
