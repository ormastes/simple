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

## 2026-05-07 Remade Plan For WM X11 And Executable Environment

Current answer:

- WM supports a Wine-facing X11-class interface contract over SimpleOS window records, framebuffer presents, cursor evidence, clipboard evidence, properties, and FIFO events. It is not a full X server or complete Xlib/XCB protocol endpoint.
- SimpleOS supports Wine readiness evidence for a full-OS executable environment through QEMU boot, process-backed execution, VM space, filesystem, window system, network, container namespace facets, and an NVFS-backed container rootfs. It is not arbitrary full Wine/PE compatibility.

Next acceptance criteria:

1. X11 production binding must require SimpleOS cursor and clipboard evidence in addition to window/framebuffer lifecycle evidence.
2. Container executable-environment evidence must prove pid, fs, ipc, net, and capability namespace facets separately.
3. Container rootfs evidence must name the NVFS backend before the Wine `exec_env` row can be verified.
4. Tests must keep coarse marker-only logs blocked with structured first-missing states.

## Result (DONE 2026-05-07)

Implemented in `src/lib/common/ui/wine_simpleos_window_bridge.spl`, `src/lib/common/ui/wine_x11_adapter.spl`, `src/lib/common/wine_vm_adapter.spl`, `src/lib/common/wine_image_vm_map.spl`, and `src/lib/common/wine_hello_exe.spl`.

Verified 2026-05-07:

- `wine_x11_adapter_spec.spl`: 11 examples, 0 failures.
- `wine_image_vm_map_spec.spl`: 3 examples, 0 failures.
- All implementing files present and lint-clean.
- Acceptance criteria 1-5 met: production gates require SimpleOS window/framebuffer/cursor/clipboard evidence; VM gates require process id, address-space id, container namespace facets, OS VMA mapping, stack/guard, fault evidence, and no-host-code-jump; hello.exe maps PE into VM process; tests distinguish modeled vs production; audit names residual blockers.

This plan is complete. Full Wine graphics driver integration and kernel page-table enforcement remain intentionally blocked.
