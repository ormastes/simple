# UI slim pack inventory (A10)

**Package:** A10 of `doc/03_plan/ui/slim_kernel_plugin/plan.md` ("A10 pack
closure" / "A10 SMF pack placement"), reduced to what is measurable now: a
feature-pack **inventory**, not an enforcement gate and not a pack loader.
Design context: `doc/05_design/ui/slim_kernel_plugin/design.md` §"Composition
recipes" (`tui-hello-static`, `gui-hello-static`) and the external design's
§5.2/§7 placement table in
`doc/01_research/ui/slim_kernel_plugin/simple_slim_tui_gui_kernel_plugin_design_parallel_plan_2026-09-05.md`.

## What it is

`scripts/check/check-ui-slim-pack-inventory.shs` runs `deps fast` on each
product entry (same extraction approach as
`scripts/check/check-ui-slim-closure.shs`: parse `src/`-prefixed tokens out of
`deps fast` output, and fail closed — ERROR, not a silent pass — on an
unresolved bare-rooted or dotted-directory import edge), then classifies every
file in that real closure into a named **pack** by path prefix, using the
prefix table in `config/ui/pack_prefixes.sdn`. It prints one table per entry
(`pack  files  state`, state = `required` if the closure carries >=1 file
under that prefix, else `absent`), then a `## Recipe check` section per entry
comparing the inventory against the design's two sealed recipes:

- **`tui-hello-static`**: `compositor`/`drivers`/`kernel`/`skia`/`gpu` must all
  be `absent`; `parser` is required only when the entry is file-driven, which
  the script reports informationally rather than enforcing (it cannot tell
  "file-driven" from the closure alone).
- **`gui-hello-static`**: `compositor` must be `absent`; at most one of
  `skia`/`gpu` may be `required` (one renderer).

Every non-`other` prefix in the config is verified to exist on disk before any
entry is scanned — a prefix that does not exist is a **stale-config ERROR**,
not a silently-empty pack, so the config cannot quietly drift from the real
tree. The verdict is always the last stdout line: `PASS — <n> entries
inventoried, 0 violations` / `FAIL — ... <k> violations: <entry:pack, ...>` /
`ERROR — nothing was checked (<reason>)`. `--selftest` runs 4 fixtures (clean
TUI closure -> PASS, compositor-in-TUI-closure -> FAIL naming it, a stale
prefix -> ERROR, an empty `deps fast` result -> ERROR) and is fatal.

## Prefix shapes and full-product entries (2026-09-06)

A pack prefix may be a directory or a single module file: `layout`, `widgets`,
`session`, and `draw_ir` resolve to `<prefix>.spl` (`src/lib/common/ui/layout.spl`,
`widget.spl`, `src/lib/nogc_sync_mut/ui/session.spl`, `draw_ir*.spl`), so the
existence check accepts either. Entries whose product is the shared-WM TUI or a
web/browser/electron/tauri backend are classified under `ui-full-static` (no absence
rule; counts reported) instead of the hello recipes. Measured 2026-09-06 with the seed:
`PASS — 6 entries inventoried, 0 violations`; the shared-WM TUI carries compositor 20 /
drivers 10 / kernel 10 / skia 20 / gpu 68 files by design, the web backend
compositor 20 / drivers 36 / kernel 36 / skia 20 / gpu 68.

## Report, not a loader

No pack loader exists (`doc/03_plan/ui/slim_kernel_plugin/plan.md`: "static
composition until dynSMF reopen gates pass"). This inventory is read-only
evidence for the A10/A11 certification wave — it does not gate `simple test`,
does not change build output, and carries no runtime behavior of its own.
