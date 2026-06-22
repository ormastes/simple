# GUI Showcase 4K 200 FPS JIT Lowering Blocker

- Date: 2026-06-22
- Status: open
- Gate: `scripts/check/check-widget-showcase-4k-200fps.shs`
- Evidence: `build/widget-showcase-4k-200fps/status.env`

## Problem

The 4K widget showcase performance gate cannot reach the requested 200 FPS
through either available fast path.

Interpreter/JIT path falls back to the interpreter:

```text
HIR lowering error: Memory safety error [W1006]: mutation without mut capability:
mutation requires `mut` capability while lowering _emu_sort_i32 at 75:24
```

Native alias path builds, but the compiled Engine2D CPU path crashes before
readback:

```text
gui_showcase_4k_200fps_status=fail
gui_showcase_4k_200fps_reason=native-showcase-probe-failed
gui_showcase_4k_200fps_probe_exit_code=139
```

The app-specific `W_dot_to_u32`/`H_dot_to_u32` unresolved native stubs were
removed from `widget_showcase_gui.spl`, but `two_line_2d_gui.spl` compiled with
the same native-build settings also segfaults after `CpuBackend` startup. This
points at the native Engine2D CPU backend/runtime path, not only the showcase.

## Required Fix

Fix the Simple native/JIT lowering path for the imported Engine2D/UI dependency
chain and the native Engine2D CPU backend crash, or route the gate to a
repo-approved Metal/Vulkan compiled alias with equivalent widget-showcase
readback evidence. Do not claim the 4K/200 FPS target from the interpreter
fallback or a crashing native binary.
