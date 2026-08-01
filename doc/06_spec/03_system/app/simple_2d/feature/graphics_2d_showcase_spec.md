# Graphics 2D showcase hardening

This SPipe contract guards the owners required for the 2D showcase. It is not
a substitute for live acceptance.

## Ordered WM planes

The gallery must use the Engine2D `Layer` and `Compositor` APIs and render the
resulting desktop, child-window, and taskbar image. The insertion order is
intentionally different from z-order, so the displayed pixels prove ordering.

## Normalized interaction

Host batches must enter `WindowEventLoop` as key, pointer-move, and
pointer-button records, then be drained before interaction state is counted or
rendered. Raw Winit counters cannot satisfy this scenario.

## Vector and performance proof

The showcase must preserve its selected vector-face/warm-cache proof and its
changed-frame performance route. The live command needs >=60 redraws, p95
<=33.33 ms, and a changed checksum. If startup prevents a receipt, status is
pending—not pass.

Source: `test/03_system/app/simple_2d/feature/graphics_2d_showcase_spec.spl`.
