# simple_web readiness marker is aspirational; diskless desktop boots never render web content

- **ID:** simple_web_readiness_marker_aspirational_diskless_2026-07-20
- **Status:** OPEN
- **Severity:** medium (check-honesty: readiness line overstates surface state; web surface unverified in-guest)
- **Found by:** WEB-CHECK surface verification lane, 2026-07-20

## Findings
1. `[production-readiness] ... simple_web=content-frame` is a **hardcoded
   literal** in examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl:531,
   printed unconditionally once the readiness gate passes — not computed
   from live web-content state. On the current evidence boots it is
   asserted while zero web content exists on screen.
2. The boot harness is diskless for apps: `[vfs-init] hosted fat32 mount
   skipped: blockdevice-dispatch-codegen-bug` → `owned_surface_count=0` →
   degraded-no-disk branch → the single large window is a generic
   "System Console" (shell.ensure_baremetal_system_window), not a
   browser_demo surface. No `materialize` line appears in the whole log.
3. The window's content area renders `0xFF182230` — the empty-content
   fallback bg (window_scene_draw_ir.spl:1032), old dark palette
   (Aqua migration of that fallback is queued separately).
4. Hosted parity check check-simple-web-engine2d-js-bitmap-evidence.shs
   FAILS with mismatch_count=2304/6144 on scene
   simple-web-engine2d-image-taskbar-command — LIKELY a **stale node-side
   baseline** vs the landed Aqua palette + 4x4 AA glyph changes (the scene
   includes taskbar+text), not a renderer defect; needs coordinated
   re-baseline, same class as the cross-backend parity fixtures skipped in
   the Aqua sweeps.

## Related
doc/08_tracking/bug/browser_demo_frozen_loading_placeholder_2026-07-12.md
(even a materialized browser_demo only ever shows a frozen placeholder).

## Fix direction
- Compute the readiness line's per-surface claims from live state (e.g.
  content-frame count > 0) or rename the marker to declare configuration,
  not state.
- Root-fix the fat32 blockdevice-dispatch codegen bug so app surfaces can
  materialize in evidence boots; then re-verify web content on screen.
- Re-baseline the js-bitmap parity scene against the Aqua+AA renderer once
  intentional-change review confirms the deltas are all theme/AA.
