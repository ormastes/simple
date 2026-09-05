# WM Full-Stack Demo System Test Plan

Executable spec: `test/03_system/wm/wm_full_stack_demo_spec.spl`

Generated manual:
`doc/06_spec/03_system/wm/wm_full_stack_demo_spec.md`

## Primary Scenario Steps

1. Start the desktop and verify a non-black sequenced frame.
2. Open the pinned demo application.
3. Verify every required GUI/Web/2D region.
4. Activate the button and verify status revision.
5. Type and edit text through key plus committed-text events.
6. Drag the nested 2D rectangle.
7. Scroll by wheel and thumb.
8. Drag the outer window titlebar.
9. Maximize and restore exact geometry.
10. Minimize and restore through the taskbar.
11. Unpin and repin by stable app ID.
12. Close and verify all handle counts return to baseline.

Run the same semantic sequence against headless and GLFW. The GLFW row also
requires real backend identity, native input receipt, and visual capture.

## Failure Scenarios

- Queue overflow preserves existing FIFO events and increments dropped count.
- Stale handles fail.
- Unsupported operations return unsupported.
- Key shortcuts do not become committed text.
- Closing/minimizing a captured target cancels capture.
- Invalid content size/checksum/origin is rejected.

## Compiler Regressions

Use the existing strict native parity harness for a compound aggregate fixture,
add a freestanding/QEMU microkernel row, and add a live entry-closure negative
link case. Do not edit active compiler implementation files in this lane.
