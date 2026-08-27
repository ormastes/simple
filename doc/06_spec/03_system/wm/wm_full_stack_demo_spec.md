# WM Full Stack Demo — Runtime Evidence Manual

Status: **RED**

Executable specification:
`test/03_system/wm/wm_full_stack_demo_spec.spl`

## Required evidence

The release gate is one runtime receipt per lane, containing:

- executable/compiler provenance and backend identities;
- frame sequence plus scene/content revisions;
- non-black framebuffer evidence and stable semantic crop checks;
- normalized input receipts and focused window/widget;
- exact maximize/restore geometry;
- persisted pinned/running taskbar state;
- mixed PCM frame count/checksum and underrun count;
- window, event, text, content, pixel, and audio handle baselines after close.

Source scans and this manual are not evidence.

## Current result

The deterministic headless scenario exists and exercises the canonical event
queue, GUI/Web/pixel content frames, WM lifecycle, cleanup, and stable `app_id`
pin persistence. It now also routes normalized pointer/key/committed-text
events through WM chrome and the GUI reducer and records deterministic
48-kHz stereo PCM evidence. Its full dependency closure is currently blocked before test
execution by the unrelated parser error recorded in
`doc/08_tracking/bug/wm_native_regression_gate_blocked_2026-07-29.md`.

The GLFW C loader self-check passes and correctly reports unavailable when the
host GLFW library is missing. The miniaudio C self-check accepts owned PCM,
starts playback, and returns playback handles to baseline. No live GLFW
screenshot/input receipt has been captured on this machine, so the host release
gate remains RED.
