# Guest CSS theme loads (bytes=1276 loaded=1) but chrome colors never change

- **ID:** wm_theme_css_loaded_not_applied_2026-07-20
- **Status:** OPEN
- **Severity:** medium (CSS-file theming works host-side end-to-end; in-guest the load rung is proven but application is dead)
- **Found by:** GRADIENT-DRAWIR lane Boot B, 2026-07-20

## Evidence

## 2026-08-01 host and render-identity remediation

The host and shared rendering defect is fixed locally: a valid CSS override
now derives an effective active `ThemeRenderSnapshot`, so DrawIR, theme-install
wire, backend clear color, browser cache keys, and Simple Web retained-content
revisions observe the override material hash rather than the original package
snapshot. The exact chrome register is retained for CSS-only slots such as
`--wm-error`.

Focused self-hosted tests passed: CSS wiring 7/7, SimpleOS bootstrap 3/3,
hosted bootstrap contract 11/11, Simple Web compositor 24/24, and browser
theme-cache identity 3/3. The bug remains OPEN only for real guest QEMU
pixel/event capture across `/THEME.CSS` boot paths; that work is assigned to
the QEMU plan/host rather than this hosted renderer lane.

## 2026-08-01 Web serialization follow-up

The earlier snapshot repair initially changed only material identity. Review
found the Web serializer still read the package `composed_css`, so a valid
override could invalidate a cache while emitting the old CSS pixels. The
effective snapshot now appends one final canonical CSS palette block (WM plus
the existing `ui`/`app` aliases), and both normal and install-wire Web documents
consume it. Hosted receipt revisions mix the material SHA-256 as well as the
source manifest. Native consumers were also moved off the known broken optional
snapshot aggregate ABI. Focused tests cover the normal/wire CSS text and
material-only revision delta; guest visible capture remains open.

Boot B (OVMF, fat32-theme.img carrying the slate_dark palette
`#0f172a`/`#1e293b`/`#2050a0` as /THEME.CSS): serial prints
`[desktop-gui] theme bytes=1276 loaded=1` — the VFS allowlist fix works,
the file is read, `wm_chrome_colors_from_css_text` is invoked and
`register_wm_chrome_theme` is called before the first frame. Yet the
rendered frame is byte-identical to Boot A in all three probe regions:
desktop `#5a7fb5`, body `#182230`, titlebar `#dceafb` — pure Aqua defaults.
0 exceptions, desktop-ready, clock-region sha unchanged.

## Suspects (in likelihood order)
1. `wm_chrome_colors_from_css_text` (src/lib/common/ui/wm_theme_css.spl)
   parse returning defaults in-guest — the byte-scan parser is host-proven
   but may hit a freestanding text/bytes landmine (e.g. the documented
   char_at-on-dynamic-strings class) and silently fall back.
2. `register_wm_chrome_theme` / `_wm_chrome_override` staleness: consumers
   may have already snapshotted `wm_chrome_theme()` values (module-init or
   first-call caching) before registration, so the override never reaches
   the draw path.
3. The live chrome path (`_wm_draw_ir_window_batch`) reading theme fields
   through a path that bypasses the override hook entirely.

## Repro / next probe
One gated serial probe in-guest: print (a) parsed token count + first parsed
color from `wm_chrome_colors_from_css_text`, (b) `wm_chrome_theme().desktop_bg`
AFTER registration, (c) the desktop_bg value the compositor actually uses at
first frame. Whichever link disagrees names the fix. Host-side control: the
same CSS text through the same fns flips all 6 slots (proven 9351608392d).

## Note
The guest wiring source in gui_entry_desktop.spl was lost to a parallel-
session WC clobber after the evidence ELF was built; it must be re-applied
(reconstruction + rebuild + one boot) before this bug's probe can run.

## 2026-07-29 confirmation (IDE extension kernel campaign, lane L5, source-level only)

Re-verified against the current working copy while investigating a related
"guest loads/registers theme but first frame stays default Aqua" report.
Two independent findings, both source-level (no QEMU boot run in this pass
— out of this lane's lib-side scope):

1. **The CSS-file wiring described in this bug's "Note" has still not been
   re-applied.** `grep -rn wm_chrome_colors_from_css_text src/ examples/`
   finds exactly one hit: the function definition itself in
   `src/lib/common/ui/wm_theme_css.spl`. Zero callers anywhere in the tree.
   That module's own header (`wm_theme_css.spl:23-31`) confirms this is
   still deliberate, not a regression: "Design note (in-guest consumption,
   not wired this pass) ... Not wired here because the guest module-init
   and VFS read-before-mount ordering are still landmines tracked
   separately." So Suspect 1/2/3 in this bug's original list are all
   moot for the CSS-file path specifically — there is no in-guest call site
   at all yet, so nothing can be silently falling back.

2. **The separate generated-snapshot path is, unlike the CSS-file path,
   fully wired.** `install_generated_simpleos_wm_theme()`
   (`src/os/compositor/simpleos_wm_theme_bootstrap.spl:13`) is called from
   all four freestanding desktop entries (x86_64 desktop + engine2d, arm64
   desktop, riscv64 desktop) before compositor construction, and both
   consumer paths — `wm_chrome_theme()` (desktop/taskbar/background fills,
   `src/lib/common/ui/wm_chrome_theme.spl:70`) and
   `active_wm_theme_snapshot_present()`/`_unchecked()` (per-window
   titlebar/body boxes, `src/lib/common/ui/window_scene_draw_ir.spl:1014`)
   — read the exact same two module-level override globals
   (`_wm_chrome_override`, `_active_theme_render_snapshot`,
   `wm_chrome_theme.spl:67-68`) that the install call writes. Source
   inspection found no defect in this path.

If the "stays Aqua" symptom being chased is about a **custom CSS theme**,
finding (1) is the root cause and the fix is exactly what this bug's "Note"
already says: wire the VFS-mounted theme file read through
`wm_chrome_colors_from_css_text()` + `register_wm_chrome_theme()` in the
guest entry points, after VFS mount and before first frame — once the
mount-ordering landmine referenced in `wm_theme_css.spl` is resolved.

If the symptom is about the **default Aetheric-dark theme** not appearing
(no custom CSS involved), source inspection did not find why — call order,
writer, and both readers all agree at the source level. That would point at
a cross-call staleness of the module-global override specifically under the
freestanding native build (the same general class of bug as the
ENTRY-module `use`-import owner-binding gap fixed for the *interpreter*
path in the 2026-07-29 stage4-memory-harden campaign, though that fix did
not target freestanding native codegen). The next step is the gated serial
probe this bug's own "Repro / next probe" section already proposes: print
`_wm_chrome_override.len()` / `_active_theme_render_snapshot.len()`
immediately after `apply_theme_render_snapshot_to_wm_chrome()` returns at
boot, and again from inside the first `wm_chrome_theme()` call at render
time, on a real QEMU boot. Not run in this pass (app-file/QEMU-infra work,
outside lane L5's lib-side-only scope).

## 2026-07-29 host-side wiring closed (IDE extension kernel campaign, lane F2)

Closed the gap finding (1) above named: `wm_chrome_colors_from_css_text` had
zero callers anywhere. Added the missing lazy-apply wiring, host-safe (no
fs/env access, so it stays freestanding-pullable):

- `apply_wm_css_theme_text(content: text) -> bool`
  (`src/lib/common/ui/wm_theme_css.spl`) — parses `content`, and only calls
  `register_wm_chrome_theme()` when at least one of the 6 `--wm-*` tokens
  actually parsed. Empty/garbage text is a no-op (returns `false`) and
  whatever chrome theme was already active — byte-identical defaults, or an
  earlier package/snapshot install — is left untouched. This closes the
  "given empty/garbage CSS, defaults survive" requirement without the naive
  approach of always registering a would-be all-defaults `WmChromeColors`,
  which would have silently reverted an already-installed non-default theme
  (e.g. the guest's generated Aetheric snapshot) back to Aqua.
- `apply_simpleos_css_theme_override(css_text: text) -> bool`
  (`src/os/compositor/simpleos_wm_theme_bootstrap.spl`) — the guest-side
  call point that hands off to the function above, documented to be called
  after `install_generated_simpleos_wm_theme()` and after VFS mount.

Proof (unit spec, `bin/simple test`, no QEMU):
`test/01_unit/lib/common/ui/wm_theme_css_wiring_spec.spl` — known CSS text
flips all 6 chrome slots including through the guest call point; empty and
garbage CSS text leave byte-identical defaults *and* a previously-installed
non-default theme untouched (register-then-garbage-apply regression case).

**What is still NOT done, and NOT claimed fixed:**
- No caller anywhere reads `SIMPLE_WM_THEME_FILE` (hosted) or a mounted
  `/THEME.CSS` (guest) and passes the bytes to these functions yet. That
  fs/env read + real call-site wiring belongs in
  `src/os/compositor/host_wm_theme_bootstrap.spl` /
  `src/os/hosted/hosted_entry.spl` (hosted) and
  `examples/09_embedded/simple_os/arch/*/gui_entry_desktop.spl` (guest) —
  none of which are in this lane's ownership scope, so they were
  deliberately not touched. Filed as follow-up: wire
  `apply_wm_css_theme_text(file_read(env_get("SIMPLE_WM_THEME_FILE")))`
  into the hosted boot path, and `apply_simpleos_css_theme_override(...)`
  into each guest `gui_entry_desktop.spl` after its VFS mount, once the
  guest module-init/VFS read-before-mount ordering landmine is resolved.
- **Guest path is explicitly NOT verified.** No QEMU boot was run in this
  pass. This lane only proves the host-safe primitives are correct and
  garbage-safe at the unit level; original Suspects 1-3 for the in-guest
  render-time symptom remain open per the confirmation section above.
