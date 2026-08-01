# SimpleOS Desktop-With-Apps Framebuffer Baseline (SYS-GUI-006 with-apps variant)

This directory holds the checked-in PPM baseline for
`test/system/simpleos_desktop_with_apps_framebuffer_spec.spl`. The spec boots
the same `desktop_e2e_entry.spl` target as the bare-desktop baseline
(`test/09_baselines/simpleos_desktop_framebuffer/`), but waits for the
`remote-grouping:ok` marker so the two default demo apps are open before
capture.

## Files

- `desktop_with_apps_scene.ppm` - 1024x768 P6 PPM golden image, intended to
  show the desktop with app windows open.

## STATUS: BLOCKED (2026-07-20, task #6 Aqua+glyph baseline refresh)

**Not regenerated this pass.** Blocked on the same crash documented in
`test/09_baselines/simpleos_desktop_framebuffer/README.md`: the real
generator entry, `examples/09_embedded/simple_os/arch/x86_64/desktop_e2e_entry.spl`,
faults deterministically during early boot (page-table allocator panic trap
in `kernel__arch__x86_64__paging___alloc_table_page`, before even reaching
`[desktop-e2e] launcher-ready apps=5`) — so it never gets far enough to open
app windows, let alone reach `remote-grouping:ok`.

Unlike the bare-desktop baseline, no stand-in was substituted here. The
alternate `gui_entry_desktop.spl` boot used for that stand-in (via
`build/os/_wkheap/desktop.elf`) is diskless in the harness used this pass
(`build/os/_wkheap/diag-verdict.out` shows `degraded_window_count=0
skipped=1` — the shell renders its own chrome windows but no app windows are
launched), so it cannot stand in for an "apps open" scene without misleading
the reader further than the bare-desktop stand-in already does. The existing
`desktop_with_apps_scene.ppm` is left as-is (pre-Aqua; verified byte-identical
to the pre-refresh bare-desktop baseline, sha256
`2280508107563e3472a72485662e4e7e4b34252fd648fc4b4a0f563eda4ea996` — it looks
to have been a copy/stub rather than a distinct real capture even before this
pass).

**To unblock:** fix the `desktop_e2e_entry.spl` boot crash (see the bare-desktop
README for full diagnostic detail), confirm the disk-backed launcher can open
the two default demo apps (`build/os/fat32-x86_64.img` already carries the
required app manifest markers —
`browser_demo_remote_main`/`hello_world_remote_main`/`file_manager_remote_main`/
`shell_remote_main`/`editor_remote_main`/`smux_remote_main` — so the disk
fixture itself is not the blocker), then run
`UPDATE_BASELINE=1 bin/simple test test/system/simpleos_desktop_with_apps_framebuffer_spec.spl`
*after* the bare-desktop baseline has been confirmed correct with a real
capture.
