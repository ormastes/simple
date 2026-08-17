# GLFW event draining could starve rendering

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Affected owner:** `runtime_glfw.c` / `SimpleGlfw.poll_events()`
- **Impact:** sustained native input could keep one WM poll call running and
  prevent the next render or routing step.

## Root cause

`SimpleGlfw.poll_events()` repeatedly called `rt_glfw_poll_event()` until it
returned no event. That runtime function called `glfwPollEvents()` before every
single FIFO pop. New native events could therefore be appended as quickly as
the facade removed them, making the drain unbounded.

## Fix

The runtime now separates:

```text
rt_glfw_pump_events()  -> one native GLFW pump
rt_glfw_pop_event()    -> one existing FIFO record, no native pump
```

The Simple facade pumps once and then drains only the finite queued snapshot.
`rt_glfw_poll_event()` remains as a compatibility pump-plus-pop wrapper for
older direct C callers.

## Evidence

- Runtime no-display selfcheck compiled and exited `0`.
- Xvfb live probe received real key, committed text, pointer motion, and button
  input using the split API:
  `glfw_live_probe=pass packed_argb32=1 frames=2
  native_input=key,text,pointer,button`.
- The full Simple WM demo closure linked with the new runtime object
  (`3 compiled / 511 cached`). This proves the Simple facade and C ABI agree;
  it is not a new rendering-completeness claim.

## Remaining event work

SDL2 still exposes only one mutable `g_last_event`, so it cannot preserve a
multi-event batch or owned text payloads. SimpleOS committed text is now a
separate WM event; live QEMU evidence remains a separate follow-up gate.
