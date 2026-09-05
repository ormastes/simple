# SimpleOS x86_64 desktop entry did not share the font-bootstrap owner

**Status:** Fixed in source (static verification only — not run on hardware or
under QEMU in this pass).

## Symptom

`os.desktop.font_bootstrap.simpleos_desktop_register_selected_fonts_from_vfs()`
is the shared owner that walks every pinned font candidate and registers it
with the `FontRenderer`. ARM64's and RV64's `gui_entry_desktop.spl` call it
(`arm64`: import + `val font_loaded =
simpleos_desktop_register_selected_fonts_from_vfs()`; `riscv64`: same). The
x86_64 entry did not: it re-implemented a single-face variant inline —
reading `/SYS/FONTS/NOTOSANS`, calling `engine.load_font_bytes(...)`, then
`font_renderer_register_selected_bytes(...)` — instead of reusing the shared
owner. `git grep -c simpleos_desktop_register_selected_fonts_from_vfs` on
`examples/09_embedded/simple_os/arch/{arm64,riscv64}/gui_entry_desktop.spl`
returned 2 each (import + call); the same grep on
`arch/x86_64/gui_entry_desktop.spl` returned 0.

This left x86_64's font registration free to drift from the shared,
multi-face-aware owner used by the other two architectures, and made a prior
bug write-up's claim that "both" desktop entries reuse the shared owner false
for x86_64 at the time it was written.

## Fix

`arch/x86_64/gui_entry_desktop.spl` now imports and calls
`simpleos_desktop_register_selected_fonts_from_vfs()` right after the FAT32
VFS mount, before continuing into its own scanout/engine setup — the same
point in program order ARM64 calls it, relative to its VFS mount. The
now-redundant single-face `font_renderer_register_selected_bytes(...)` call
was removed; the local `engine.load_font_bytes(...)` diagnostic path (SHA-256
+ sfnt-table re-validation, name decode probe) that feeds the
`taskbar-clock` font-evidence line is unchanged and still runs, renamed to
`engine_font_loaded` to avoid colliding with the new outer `font_loaded`.

This is **not** a fail-closed change: x86_64 still falls back to
`[desktop-gui] font unavailable fallback=bitmap` if the local diagnostic path
fails, exactly as before. Only the shared-owner call was added; no bitmap
fallback branch was removed.

## Regression

`test/01_unit/os/gui_entry_desktop_production_render_contract_spec.spl` and
`test/02_integration/os/port/simpleos_font_asset_staging_spec.spl` already
assert `arch/x86_64/gui_entry_desktop.spl` contains
`val font_loaded = simpleos_desktop_register_selected_fonts_from_vfs()`
(ordered before `create_fb_engine_sized(...)` and before the first frame) and
does **not** contain `font_renderer_register_selected_bytes(`. Both specs
were red against this file before this fix landed.

## Verification

Static only: confirmed by source grep and by the two specs above encoding the
exact expected call site and ordering. No QEMU boot or hardware run was
performed as part of this change — this is not runtime evidence that font
registration succeeds on target.
