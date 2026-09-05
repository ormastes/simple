# `apply_wm_action_to_lifecycle_windows` "restore" action does not restore window geometry

Date: 2026-08-08
Component: `src/os/compositor/wm_action_lifecycle.spl`
Status: open (filed, not fixed — currently dead code, see "Reachability" below)

## Summary

`apply_wm_action_to_lifecycle_windows` (wm_action_lifecycle.spl:285) handles
`WmAction.kind == "maximize"` by overwriting the window's `x/y/w/h` to full
desktop bounds (lines 328-336), but the paired `"restore"` branch (lines
337-341) only clears `minimized`/sets `focused` — it never restores `x/y/w/h`
to their pre-maximize values:

```
elif action.kind == "restore":
    win.minimized = false
    win.focused = true
    out_windows[i] = win
    return WmLifecycleApplyResult(windows: wm_lifecycle_focus_window(out_windows, action.window_id.to_i64()), next_window_id: next_id, window_id: action.window_id.to_i64(), applied: true)
```

The root cause: `WmLifecycleWindowState` (defined via
`host_window_to_lifecycle_state` / `host_window_from_lifecycle_state`,
host_compositor_core.spl:2384-2388) carries only `id, owner_port, title, x, y,
w, h, content, process_id, app_id, content_owner, minimized, focused` — no
`maximized` flag and no `restore_x/y/w/h` fields. So even if the `"restore"`
branch wanted to restore geometry, the model it operates on has nowhere to
have stashed it. Maximize here is a one-way, irreversible geometry overwrite.

Compare this to the *correct* real implementation living one layer up, on
`HostCompositor` itself (host_compositor_core.spl `me maximize_window` /
`me restore_window`, lines 1744-1796), which DOES carry `win.maximized` +
`win.restore_x/y/w/h` on `HostedWindow` and correctly round-trips geometry.

## Reachability (why this is FILE not FIX-NOW)

Today this is dead code, not a live-traffic bug:
- The only place a `WmAction(kind: "maximize"/"restore", ...)` is constructed
  is `wm_action_from_bridge_request` (wm_action_lifecycle.spl:371-374).
- Its only caller, `HostCompositor.apply_bridge_request`
  (host_compositor_core.spl:1724), explicitly intercepts
  `COMP_MAXIMIZE`/`COMP_RESTORE` (lines 1726-1741) and calls the correct
  `self.maximize_window()` / `self.restore_window()` methods directly,
  `return`-ing before ever reaching the `self.apply_wm_action(action)`
  fallthrough at line 1742 that would route into the broken lifecycle path.
- Grep across `src/app/` and `src/os/` for `apply_wm_action(` (the only entry
  point into `apply_wm_action_to_lifecycle_windows`) found exactly three call
  sites: the bridge-request fallthrough above (unreachable with maximize/
  restore kind), and two `wm_destroy_action`/`wm_focus_action` calls
  (host_compositor_core.spl:1887,1890) — neither constructs a maximize/
  restore action.

So no reachable path currently drives `kind == "restore"` into
`apply_wm_action_to_lifecycle_windows`. This is exactly the kind of latent
trap the "delegating wrapper that looks complete" pattern warns about: the
function *looks* like a correct maximize/restore state machine (it has both
arms, both return through the same `wm_lifecycle_focus_window` helper) but
one arm is silently a no-op relative to its sibling, and the moment any new
caller constructs a `WmAction(kind: "restore", ...)` directly (bypassing
`apply_bridge_request`'s method-code interception) — e.g. a future WmAction
producer, a test harness, or a websocket/remote-protocol path added later —
that caller's windows get stuck at maximized bounds on "restore".

## Repro (function-level, not end-to-end reachable today)

```
val w0 = WmLifecycleWindowState(id: 1, owner_port: 1, title: "t", x: 10, y: 20,
    w: 300, h: 200, content: "", process_id: 0, app_id: "", content_owner: 0,
    minimized: false, focused: true)
val after_max = apply_wm_action_to_lifecycle_windows([w0], 2, 1024, 768,
    WmAction(kind: "maximize", window_id: 1, ...))
# after_max.windows[0] = {x:0, y:WM_WORK_AREA_TOP, w:1024, h:768-...}
val after_restore = apply_wm_action_to_lifecycle_windows(after_max.windows, 2,
    1024, 768, WmAction(kind: "restore", window_id: 1, ...))
# BUG: after_restore.windows[0] is STILL {x:0, y:WM_WORK_AREA_TOP, w:1024,
# h:768-...} — never returns to {x:10, y:20, w:300, h:200}.
```

## Suggested fix (larger than a quick patch — schema change)

Add `maximized: bool` + `restore_x/y/w/h: i32` to `WmLifecycleWindowState`,
mirroring `HostedWindow`; update `host_window_to_lifecycle_state` /
`host_window_from_lifecycle_state` to carry them; update the `"maximize"`
branch to stash pre-maximize geometry (guarded by `not win.maximized`, same
as `HostCompositor.maximize_window`) and the `"restore"` branch to pop it
back, matching `HostCompositor.restore_window`'s logic exactly. This touches
the `WmLifecycleWindowState` struct definition and every constructor site
across `wm_action_lifecycle.spl` and `host_compositor_core.spl` — audited as
too wide to land as a same-session sabotage-verified fix; filed instead.

## Found during

WM/compositor ad-hoc-impl-gap audit, 2026-08-08, following on from
`doc/09_report/ui/rendering/rendering_adhoc_impl_gap_audit_2026-08-07.md`.
