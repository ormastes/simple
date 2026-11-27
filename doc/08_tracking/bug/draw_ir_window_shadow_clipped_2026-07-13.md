# Draw IR window shadow is clipped and overwritten

Status: CLOSED (verified 2026-11-25; the "open (TODO 554)" header was a stale
resurrected revision)

## Verified closed 2026-11-25 (release/1.0.0, worktree wt-p3-baf)

- The authoritative bug DB already records this entry **closed 2026-08-17**
  (`doc/08_tracking/bug/recent_bugs.md` row `draw_ir_window_shadow_clipped_2026-07-13`,
  and `doc/08_tracking/bug/data/db_hygiene_remaining_2026-11-13.md` line for
  bug_db.sdn L662: "claims open | authoritative `closed` (bugs L4711)"). The
  "Status: open (TODO 554)" line in this file was the stale side of that
  split, resurrected by the 2026-09 tree transplant.
- The owner fix described below is landed in the canonical WM Draw IR
  producer: `_wm_window_panel2d` (`src/lib/common/ui/window_scene_draw_ir.spl:1048-1063`)
  inflates the window's Panel2D embedding by
  `min(WM_WINDOW_SHADOW_OFFSET_X/Y, remaining scene space)`, so the embedded
  surface is window+shadow sized and the shadow RECT at local
  (`WM_WINDOW_SHADOW_OFFSET_X`, `WM_WINDOW_SHADOW_OFFSET_Y`) survives the
  clip; hit/layout children (body/titlebar/close) keep their original bounds.
- Executed evidence on the tracked `bin/simple.exe` (interpreter):
  `SIMPLE_LIB=src bin/simple.exe test test/01_unit/lib/common/ui/window_scene_draw_ir_panel2d_migration_spec.spl --mode=interpreter`
  → **8/8 passed**, including "a focused titled window: shadow-inflated size,
  layer = z+10, opacity 1000, clip true, surface_id preserved" and the
  borderless no-inflation control.

## Observed

The canonical WM window batch emits a translucent shadow RECT at local `(5,6)`
with the full window size, then a full-window body RECT. The embedded surface is
exactly the window size and clipped, so the body overwrites every in-bounds
shadow pixel and the displaced right/bottom pixels never leave the child.

## Owner fix

Keep the fix in the canonical WM Draw IR producer: represent the shadow with
bounds that survive the embedded-surface clip (or a separate ordered surface),
without adding a GUI-specific renderer path. Preserve hit/layout bounds and
verify identical local CPU and checked host-device output.

## Acceptance

- A pixel outside the window body but inside the declared shadow is visible.
- Window/body/content hit and clip bounds remain unchanged.
- CPU and checked Vulkan composition remain exact for focused and unfocused windows.
