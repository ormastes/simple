# Domain Research: Simple 2D Primitive Lane

Research date: 2026-08-08. External standards inform invariants only; they do
not establish Simple implementation or QEMU evidence.

## Relevant external contracts

- [W3C Pointer Events](https://www.w3.org/TR/pointerevents/) defines a
  device-neutral pointer stream and requires primary-button activation to be
  represented by `click`; this supports one common press/release activation
  path for Web, GUI, WM, and 2D.
- [CSS Overflow Module](https://www.w3.org/TR/css-overflow/) distinguishes a
  scroll container and clipped overflow; Simple should not equate clipping
  with scroll mutation.
- [Vulkan 1.4 specification](https://registry.khronos.org/vulkan/specs/latest/html/vkspec.html)
  states that queue work is asynchronous and that a signaled fence establishes
  completion/visibility of earlier writes. Device promotion therefore needs a
  fenced terminal completion before readback.

## Design implications

Pointer capture/release and keyboard activation belong to the common semantic
owner, not to a backend adapter. CSS/layout computes geometry and overflow
state before hit testing and Draw IR. Vulkan readback is valid evidence only
after explicit synchronization and must be compared with an independent CPU
oracle. These are compatibility constraints, not permission to add a parallel
renderer or browser-specific primitive API.

## Boundary

The sources above describe standards behavior. They do not prove support for
SimpleOS, the host container, Vulkan drivers, QEMU, macOS emulation, or UNO Q;
those require the repository's own tests and retained receipts.
