# SDL2 Seam-Subset Audit

**Status:** read-only audit + ratchet, 2026-08-05. Lane C of
`doc/03_plan/ui/wm_platform_honesty_agent_lanes.md`. No production code was
modified by this lane.

**Scope:** does WM/compositor code use only the seam-shaped subset of SDL2
(2D surface + events — `src/lib/nogc_async_mut/wm/host.spl`'s `WmHost2d`
trait: `surface_acquire`, `surface_present`, `surface_release`,
`event_poll`), or does it reach the extras (timers, display bounds/DPI,
window title/size/position/fullscreen, cursor grab/warp, clipboard,
lifecycle)? Compositor-scoped only — see
`doc/04_architecture/ui/wm_gui_web_dependency_audit.md` for the full
184-violation repo-wide dependency classification, which this lane does not
re-litigate.

## Answer

**Yes, compositor code reaches extras today** — but the extras it reaches are
mostly lifecycle/polling calls (`init`, `quit`, `get_mouse_x`, `get_mouse_y`),
not the timer class the dependency audit flagged as the largest removable
violation (22 edges): **`get_ticks_ms`/`get_ticks_ns` are NOT referenced
anywhere under `src/os/compositor/` or `src/lib/nogc_async_mut/wm/`** as of
this measurement. The compositor's actual extras problem is different from
what was predicted: roughly half of `hosted_backend_sdl2.spl`'s SDL2 externs
(7 of 14) and half of `hosted_input_sdl2.spl`'s (3 of 6, matching lane A4's
independent finding) are **dangling** — they name functions that do not exist
anywhere in the registered 66-entry-point surface — rather than legitimate
extras. See "Dangling externs" below.

## Method

The registered surface was enumerated by anchored grep of public (non-
`static`) `rt_sdl2_*` function definitions in `src/runtime/runtime_sdl2.c`,
cross-checked against the interpreter dispatch table in
`src/compiler_rust/compiler/src/interpreter_extern/sdl2.rs`:

```
/usr/bin/grep -E "^[A-Za-z].*rt_sdl2_[A-Za-z0-9_]+\(" src/runtime/runtime_sdl2.c \
  | /usr/bin/grep -v "^static" | wc -l
# => 66
```

The internal helper `rt_sdl2_event_code` (`runtime_sdl2.c:745`, `static`) is
excluded — `sdl2.rs` deliberately asserts it has no dispatch signature
(`signature_of("rt_sdl2_event_code").is_none()`, line 446), confirming it is
not part of the callable surface. The dispatch table's own string set matches
the C definitions exactly modulo two known non-symbols: a `"rt_sdl2_"`
prefix-check literal (`sdl2.rs:411`) and a `"rt_sdl2_not_a_real_function"`
negative-test string (`sdl2.rs:453`) — neither is a real entry point.

The 14 `.spl` callers were enumerated by:
```
/usr/bin/grep -rl "rt_sdl2_" --include=*.spl src/
```

## Registered surface: 66 entries, categorized

| Category | Count | Members |
|---|---:|---|
| `seam:surface` | 3 | `create_window`, `destroy_window`, `present_rgba` |
| `seam:event` | 13 | `poll_event`, `event_key_code`, `event_key_mod`, `event_key_sym`, `event_mouse_button`, `event_mouse_x`, `event_mouse_y`, `event_text`, `event_wheel_x`, `event_wheel_y`, `event_window_data1`, `event_window_data2`, `event_window_event_id` |
| `extra:timer` | 2 | `get_ticks_ms`, `get_ticks_ns` |
| `extra:display` | 11 | `get_num_displays`, `get_display_name`, `get_display_bounds_{x,y,w,h}`, `get_display_dpi`, `get_display_usable_{x,y,w,h}` |
| `extra:window-mgmt` | 23 | `get_window_width`, `get_window_height`, `set_window_title`, `set_window_resizable`, `set_window_fullscreen`, `set_window_fullscreen_checked`, `set_window_size`, `set_window_position`, `get_window_position_{x,y}`, `show_window`, `hide_window`, `set_window_minimum_size`, `set_window_maximum_size`, `minimize_window`, `maximize_window`, `restore_window`, `set_window_bordered`, `set_window_always_on_top`, `focus_window`, `window_flags`, `window_should_close`, `clear_quit` |
| `extra:cursor` | 3 | `set_cursor_visible`, `set_cursor_grab`, `warp_mouse` |
| `extra:other` | 11 | `init`, `quit`, `wait_event`, `is_key_pressed`, `get_mouse_x`, `get_mouse_y`, `is_mouse_button_pressed`, `last_error`, `clipboard_get`, `clipboard_set`, `clipboard_has_text` |
| **Total** | **66** | |

The **seam allowlist** (16 symbols = `seam:surface` ∪ `seam:event`) is the
literal set enforced by
`test/03_system/gui/wm_host_platform/sdl2_seam_subset_spec.spl`.

## Per-caller matrix (14 `.spl` files)

| File | Distinct `rt_sdl2_*` symbols | Verdict |
|---|---:|---|
| `src/os/compositor/hosted_backend_sdl2.spl` | 14 (7 registered, 7 dangling) | **compositor — strict** |
| `src/os/compositor/hosted_input_sdl2.spl` | 6 (3 registered, 3 dangling) | **compositor — strict** (lane A4 plans to delete this file) |
| `src/os/compositor/hosted_backend.spl` | 1 (prose-only, no extern decl) | **compositor — strict** |
| `src/lib/nogc_sync_mut/game2d/backend/sdl_backend.spl` | 2 | full-SDL2 consumer (out of contract scope) |
| `src/lib/nogc_sync_mut/game2d/input/api.spl` | 1 | full-SDL2 consumer (out of contract scope) |
| `src/lib/nogc_sync_mut/web_ui/app.spl` | 1 | full-SDL2 consumer (out of contract scope) |
| `src/lib/nogc_sync_mut/web_ui/bridge.spl` | 1 | full-SDL2 consumer (out of contract scope) |
| `src/lib/nogc_sync_mut/web_ui/input.spl` | 12 | full-SDL2 consumer (out of contract scope) |
| `src/lib/nogc_sync_mut/web_ui/window.spl` | 3 | full-SDL2 consumer (out of contract scope) |
| `src/lib/nogc_sync_mut/desktop/display.spl` | 11 (all `extra:display`) | full-SDL2 consumer (out of contract scope) |
| `src/lib/nogc_sync_mut/io/window_sffi.spl` | 67 | full-SDL2 consumer (out of contract scope) |
| `src/app/io/window_ffi.spl` | 54 | full-SDL2 consumer (out of contract scope) |
| `src/app/io/window_sffi.spl` | 54 | full-SDL2 consumer (out of contract scope) |
| `src/compiler/70.backend/backend/runtime_compiler.spl` | 1 | full-SDL2 consumer (out of contract scope; compiler-side registration, not a runtime caller) |

Only the 3 compositor rows are in the ratchet's scan scope
(`src/os/compositor/**/*.spl`, `src/lib/nogc_async_mut/wm/**/*.spl` — the
`wm/` tree currently has **zero** `rt_sdl2_*` references of its own, verified
by `grep -rn "rt_sdl2_" src/lib/nogc_async_mut/wm/`).

## Compositor-scope detail

### `hosted_backend_sdl2.spl` (14 externs declared, lines 3–16)

| Symbol | In registered 66? | Seam? | Baseline tag |
|---|---|---|---|
| `rt_sdl2_init` | yes | no | `extra:other` |
| `rt_sdl2_quit` | yes | no | `extra:other` |
| `rt_sdl2_create_window` | yes | **yes** | — (allowlisted) |
| `rt_sdl2_destroy_window` | yes | **yes** | — (allowlisted) |
| `rt_sdl2_poll_event` | yes | **yes** | — (allowlisted; see arity note below) |
| `rt_sdl2_get_mouse_x` | yes | no | `extra:other` |
| `rt_sdl2_get_mouse_y` | yes | no | `extra:other` |
| `rt_sdl2_clear` | **no — dangling** | — | `dangling` |
| `rt_sdl2_fill_rect` | **no — dangling** | — | `dangling` |
| `rt_sdl2_present` | **no — dangling** (the real symbol is `present_rgba`) | — | `dangling` |
| `rt_sdl2_resize_window` | **no — dangling** (the real symbol is `set_window_size`) | — | `dangling` |
| `rt_sdl2_get_event_type` | **no — dangling** | — | `dangling` |
| `rt_sdl2_get_key_code` | **no — dangling** | — | `dangling` |
| `rt_sdl2_get_mouse_button` | **no — dangling** | — | `dangling` |

Half of this file's SDL2 surface (7 of 14 declared externs) names functions
that do not exist in `runtime_sdl2.c` under any name — not "extra beyond the
seam", but simply broken. Any code path through `clear`/`fill_rect`/
`present`/`resize_window`/the polled-event decode trio fails at the extern
boundary. The seam's real `present_rgba` is declared nowhere in this file, so
the compositor's SDL2 backend cannot actually present a frame through the
honest entry point today.

**Arity note (not in scope to fix):** this file declares
`rt_sdl2_poll_event(handle: i64) -> i64`, but the real C signature is
`rt_sdl2_poll_event(void)` (no arguments) — see `runtime_sdl2.c:771`. This is
a separate defect from the "dangling" list above (the symbol name matches,
the signature doesn't) and is left for whichever lane next touches this file
(not owned by any lane in the platform-honesty plan as written — flagged
here so it is not lost).

### `hosted_input_sdl2.spl` (6 externs declared, lines 5–10)

3 of 6 dangling (`get_event_type`, `get_key_code`, `get_mouse_button`) — this
matches lane A4's independent finding in the platform-honesty lane plan
("3 of 6 externs dangling, zero call sites anywhere in `src/`"). A4 plans to
delete this file; when it does, delete its 5 lines from
`doc/08_tracking/wm_sdl2_extras_baseline.txt` in the same commit (2 extras +
3 dangling — `poll_event`, `get_mouse_x`, `get_mouse_y` are seam-allowlisted
and were never baseline lines).

### `hosted_backend.spl` (0 externs declared)

The only `rt_sdl2_*` text in this file is prose: a docstring line (310) and
two comment lines (338, 342) documenting a known gap ("under the
interpreter/JIT tooling binary the `rt_sdl2_*` externs are not registered").
The spec's scanner strips full-line `#` comments but does not parse
triple-quoted docstring boundaries, so the docstring mention still earns one
conservative baseline line (`hosted_backend.spl:rt_sdl2_init:prose`) — this
is intentional (see the spec file's "Compatibility and Limitations" section):
a prose mention cannot be used to smuggle a real call past the ratchet by
wrapping it in a comment.

## The ratchet

**Files:**
- `doc/08_tracking/wm_sdl2_extras_baseline.txt` — 17 lines,
  `<path>:<symbol>:<tag>`, tag ∈ `{extra:other, dangling, prose}`.
- `test/03_system/gui/wm_host_platform/sdl2_seam_subset_spec.spl` — 4 rules:
  registered-surface-size (drift detector), compositor-scope-violations
  (the ratchet proper — dynamically discovers files under
  `src/os/compositor/` and `src/lib/nogc_async_mut/wm/`, so a new file with a
  stray extra is caught without editing the spec), baseline-hygiene (stale-
  line detector, reverse direction), and non-vacuous-exclusion (proves
  `game2d`/`web_ui`/`desktop`/`app/io` staying out of scope is not an
  accident — `desktop/display.spl` alone has 11 unbaselined extras and is
  never discovered by the compositor-scoped file glob).

**Shrink path:** the ratchet shrinks in either of two ways, both already
anticipated by other lanes in the platform-honesty plan: (a) lane A4 deletes
`hosted_input_sdl2.spl` — 5 baseline lines drop; (b) any future fix that
makes `hosted_backend_sdl2.spl`'s dangling externs resolve to real seam
symbols (e.g. wiring `present_rgba` in place of the nonexistent `present`)
moves that line from `dangling` to either seam-allowlisted (line deleted) or
a real extra (line kept, tag corrected).

## Recommendations (no code changed by this lane)

| Baseline extra | Seam-shaped replacement |
|---|---|
| `rt_sdl2_init` / `rt_sdl2_quit` | Fold into `WmHost2d.surface_acquire` / a paired teardown on `surface_release` — lifecycle belongs behind the seam's own open/close, not a bare extern call in the backend. |
| `rt_sdl2_get_mouse_x` / `rt_sdl2_get_mouse_y` (polled, not event-based) | Route through `event_poll` + the `event_mouse_x`/`event_mouse_y` accessors already in the seam allowlist instead of the polling variants — this is the same information delivered on the event path, which the seam already covers. |
| `rt_sdl2_clear` / `rt_sdl2_fill_rect` / `rt_sdl2_present` (dangling) | `present_rgba` (already seam-allowlisted) is the real, existing entry point for pushing a frame — these three dangling externs should be deleted, not fixed, once the backend is rewritten to build an RGBA buffer and call `present_rgba` instead of issuing per-primitive draw calls. |
| `rt_sdl2_resize_window` (dangling) | `set_window_size` is the real symbol; if window resize needs to reach the compositor, it should surface as a `WmHost2d`-level "surface reconfigured" signal rather than a raw SDL2 call, per the dependency audit's class-C framing (hidden precondition vs. explicit seam capability). |
| `rt_sdl2_get_event_type` / `rt_sdl2_get_key_code` / `rt_sdl2_get_mouse_button` (dangling, both files) | The real decode path is `poll_event` (already seam-allowlisted) followed by `event_key_code`/`event_key_sym`/`event_mouse_button` (already seam-allowlisted) — these dangling externs duplicate seam-shaped functionality under wrong names rather than needing a new seam capability. |
| `rt_sdl2_get_ticks_ms` / `rt_sdl2_get_ticks_ns` (in the registered surface, **not currently referenced by compositor code** — no baseline line needed today) | If a future compositor change reaches for a timer, the dependency audit's existing recommendation applies: inject a clock through the backed seam (`wm_host_2d_for_backed`), per lane A2 site-3's frozen-clock handling, rather than calling SDL2's clock directly. Recorded here so the recommendation is not lost if/when this baseline line appears. |
