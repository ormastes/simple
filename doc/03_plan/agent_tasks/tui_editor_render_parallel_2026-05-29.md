# TUI Editor Render Parallel Check - 2026-05-29

Scope: parallel TUI/editor render check for the broad Simple GUI/WM/rendering restart goal. Shared renderer files and the main restart plan were intentionally left untouched.

## Search Results

- `editor_tui_render_completion`: no current repo artifact found by exact name.
- Simple IDE/editor TUI implementation files found:
  - `src/app/editor/tui_main.spl`
  - `src/app/editor/tui_shell.spl`
  - `src/app/editor/tui_shell_panels.spl`
- Focused Simple IDE TUI render/polish spec found:
  - `test/system/editor_tui_polish_spec.spl`
- Related editor docs found:
  - `doc/03_plan/editor_ide_completion_audit_2026-05-14.md`
  - `doc/03_plan/editor_ide_production_matrix_2026-05-13.md`
  - `doc/03_plan/editor_ide_restart_plan_2026-05-13.md`
  - `doc/03_plan/editor_ide_wiki_remaining_goal_2026-05-13.md`
  - `doc/03_plan/md_editor_production_wiring.md`

## Concrete Fix

- Implemented non-stub TUI split-border drawing in `src/app/editor/tui_shell_panels.spl`.
  - Draws vertical `|` and horizontal `-` borders for adjacent split pane rectangles.
  - Uses bold style for borders adjacent to the active group, dim style otherwise.
- Updated `test/system/editor_tui_polish_spec.spl` to match the current split GUI shell file layout:
  - Drag state lives in `src/app/editor/gui_shell_core.spl`.
  - Drag handlers live in `src/app/editor/gui_shell_render.spl`.
  - TUI pane chrome lives in `src/app/editor/tui_shell_panels.spl`.

## Commands And Results

Initial focused checks:

```text
SIMPLE_LIB=src bin/simple check test/system/editor_tui_polish_spec.spl
PASS: All checks passed (1 file)

SIMPLE_LIB=src bin/simple test test/system/editor_tui_polish_spec.spl --mode=interpreter --clean --format json
FAIL: success=false, passed=0, failed=9, duration=415ms

SIMPLE_LIB=src bin/simple check test/system/editor_gui_spec.spl
WARN: 3 unresolved import warnings for std/app source-root resolution; no fatal check failure.
```

Post-fix focused checks:

```text
SIMPLE_LIB=src bin/simple check src/app/editor/tui_shell_panels.spl
PASS: All checks passed (1 file)

SIMPLE_LIB=src bin/simple check test/system/editor_tui_polish_spec.spl
PASS: All checks passed (1 file)

SIMPLE_LIB=src bin/simple test test/system/editor_tui_polish_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=9, failed=0, duration=233ms
```

## Remaining Blockers

- No dedicated `editor_tui_render_completion` plan exists yet; this note records the parallel TUI/editor slice.
- `test/system/editor_gui_spec.spl` still reports source-root/import warnings under the focused check invocation. This was not edited because it is outside the TUI render fix.
- Split-border rendering is now present for the current fallback adjacent-rect layout. Full recursive `SplitTree` ratio-driven geometry remains dependent on the broader editor split-tree/layout work.
