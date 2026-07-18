<!-- codex-design -->
# Simple WM Host and SimpleOS Fullscreen Detail Design

## Host Transition Protocol
`request_display_mode` records requested mode, saved x/y/w/h/scale, nonce, deadline, and phase without changing internal windows. Winit request success moves to `AwaitingResize`; resize and scale events update a geometry generation in either order. Matching physical state moves to `Applied`. Unsupported/denied requests, timeout, close, or exit failure move to `Failed` and roll back surface state. Repeated toggles coalesce only when nonce/mode match; stale/wrong nonces are rejected.

## Authority Snapshot Oracle
Before/during/after evidence serializes every internal window's ID, rect, z-index, focused/minimized/maximized state, app/PID, plus taskbar order/state and scene/input/taskbar revisions. Host fullscreen entry/exit must leave this snapshot byte-identical. Internal maximize/restore changes only the target rect/maximized flag and expected focus/z revision; all non-target state remains identical.

## Render Inputs
Target authority projects an immutable `SharedWmScene`. Web renderer produces `WmContentFrame` values with matching window ID, scene revision, content revision, origin `simple_web`, dimensions, checksum, and pixels. Executor rejects missing, duplicate, stale, wrong-origin, or wrong-window frames. Arbitrary runtime-created, long, and Unicode titles are passed to the real text renderer; no allowlist/template branch remains.

`WmRenderMetrics` derives from physical scale with minimum 44px logical hit targets and is shared by draw and hit-test code. Host reallocation follows acknowledged physical viewport. SimpleOS uses initialized framebuffer address/width/height/stride/format/generation; zero/invalid metadata blocks render/evidence.

## SimpleOS Input and Capture
QEMU injects keyboard/pointer events through its emulated input device path. Evidence records device kind, guest IRQ/driver event sequence, WM input revision, resulting state revision, and frame generation. Direct calls to shell action helpers are unit tests only, never system PASS evidence. QMP capture uses guest-reported scanout metadata and rejects mismatch, timeout, early exit, or partial capture.

## Failure Matrix
Unsupported/denied fullscreen, absent/out-of-order/duplicate resize-scale acknowledgement, transition timeout, close mid-transition, content failure, missing backend, silent fallback, corrupt/partial/stale report, PID/hash/window mismatch, replayed nonce/revision, input failure, QEMU exit/timeout, scanout mismatch, invalid stride/format, missing/unverified capture, and budget breach all fail closed.

## Performance Method
Reference host evidence records OS/CPU/GPU/RAM/display, revision, executable hash/version, backend, and power state. Warm startup follows one discarded launch and 10 measured launches. Frame tests discard 60 frames and measure 600; p95 uses nearest-rank over monotonic-clock durations. Mode response measures request to acknowledged physical state over 30 enter/exit pairs. RSS is sampled before and after each of 100 pairs; PASS requires final RSS <= baseline + max(16 MiB, 5%) and nonpositive least-squares growth slope over the final 50 samples. QEMU uses fixed documented machine/CPU/RAM plus idle load and measures emulated input submission to framebuffer generation over 30 pairs.

Fallback is allowed only when explicitly requested by the test row; accelerated rows fail on fallback. Typed fallback rows use the 50ms budget and record the accelerated failure separately.

## DPI/Viewport Matrix
Logical scale 1.0, 1.5, 2.0, and 3.0 at 1280x720, 1920x1080, 3840x2160, and 7680x4320. PASS requires no chrome/taskbar overlap, every control hit target >=44 logical px, title glyph ink inside bounds, and every window content rect nonzero and clipped within the viewport.

