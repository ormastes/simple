# Animation subsystems fully built and tested but unreachable in any live GUI lane

## Status
Open.

## Severity
Medium-High — honest-state documentation; animation does not meaningfully exist in production today.

## Summary
The codebase contains complete, well-designed animation machinery across three independent subsystems, all properly tested in isolation, but **zero of it runs in any live GUI**:

1. **WM spring transitions** (`src/os/compositor/animation_controller.spl`): Complete wall-clock `dt`-based spring physics animator with `animate_window_open/close/focus` helpers. `grep -rln "AnimationController"` returns only the file itself — no instantiation, no callers. Real WM open/close/focus/minimize paths snap state instantly.

2. **CSS transitions + JS rAF/timer engine** (`src/lib/gc_async_mut/gpu/browser_engine/style/animation_controller.spl` + `script/script_host.spl`): Proper `delta_ms`-driven `ActiveTransition` with easing, and `ScriptHost.tick(now_micros)` for JS-timer/rAF drainage. `grep -rn "AnimationController.new"` finds no production caller. The production `browser_script_execute.spl` entry point never calls `.tick()`.

3. **Widget bouncing-animation demo** (`src/lib/common/ui/widget_interact_model.spl:158-169`): Fixed-step `on_tick()` reducer documented as driven by a nonexistent `widget_interact_metal_gui.spl` file. Only exercised by its own spec.

## Evidence
- **animation_controller.spl**: File exists with complete implementation; reachability scan finds zero production callers, only internal self-reference.
- **host_compositor_entry.spl**: All state-change paths (destroy_window, focus_window, apply_bridge_request) execute instantly; no animator invocation.
- **script/script_host.spl:78-88**: `tick(now_micros)` method exists but is never called anywhere in `browser_engine` or production code.
- **browser_script_execute.spl**: Production JS-execution entry point; no `.tick()` call in its render-loop.
- **widget_interact_model.spl**: References nonexistent `widget_interact_metal_gui.spl`; `grep` finds no such file in current tree.

## Failure Scenario
No page with CSS transitions or JS-driven timing (splash screens, fade-in/out, staggered-reveal, debounced interactions) would animate in the browser lane. Window open/close/focus animations do not exist in the WM. The feature gap is honest — the machinery is built correctly, but there is no caller path.

## Next Step
Immediate: update documentation to not claim animation support until wiring is complete. Medium-term: wire WM animator into open/close/focus paths; drive `ScriptHost.tick()` from the web-render frame loop (after first-frame CSS perf fix lands). Related: see `browser_script_timer_deadline_absolute_relative_confusion_2026-07-05.md` for a latent bug in the timer/rAF deadline logic that would surface when wiring completes.
