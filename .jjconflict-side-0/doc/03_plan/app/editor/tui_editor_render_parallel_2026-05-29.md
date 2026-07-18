# TUI Editor Render Parallel Check - 2026-05-29

Scope: parallel TUI/editor render check for the broad Simple GUI/WM/rendering restart goal. Shared renderer files and the main restart plan were intentionally left untouched.

## Search Results

- `editor_tui_render_completion`: no current repo artifact found by exact name.
- Simple IDE/editor TUI implementation files found:
  - `src/app/editor/tui_main.spl`
  - `src/app/editor/tui_shell.spl`
  - `src/app/editor/tui_shell_panels.spl`
- Focused Simple IDE TUI render/polish spec found:
  - `test/03_system/editor_tui_polish_spec.spl`
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
- Updated `test/03_system/editor_tui_polish_spec.spl` to match the current split GUI shell file layout:
  - Drag state lives in `src/app/editor/gui_shell_core.spl`.
  - Drag handlers live in `src/app/editor/gui_shell_render.spl`.
  - TUI pane chrome lives in `src/app/editor/tui_shell_panels.spl`.

## Commands And Results

Initial focused checks:

```text
SIMPLE_LIB=src bin/simple check test/03_system/editor_tui_polish_spec.spl
PASS: All checks passed (1 file)

SIMPLE_LIB=src bin/simple test test/03_system/editor_tui_polish_spec.spl --mode=interpreter --clean --format json
FAIL: success=false, passed=0, failed=9, duration=415ms

SIMPLE_LIB=src bin/simple check test/03_system/editor_gui_spec.spl
WARN: 3 unresolved import warnings for std/app source-root resolution; no fatal check failure.
```

Post-fix focused checks:

```text
SIMPLE_LIB=src bin/simple check src/app/editor/tui_shell_panels.spl
PASS: All checks passed (1 file)

SIMPLE_LIB=src bin/simple check test/03_system/editor_tui_polish_spec.spl
PASS: All checks passed (1 file)

SIMPLE_LIB=src bin/simple test test/03_system/editor_tui_polish_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=9, failed=0, duration=233ms
```

2026-05-29 continuation:

```text
SIMPLE_LIB=src bin/simple check test/03_system/editor_gui_spec.spl
PASS: All checks passed (1 file)
```

The prior focused `editor_gui_spec` import warnings were resolved by updating
the spec to import the actual split GUI shell modules
`app.editor.gui_shell_core` and `app.editor.gui_shell_render`, and by removing
unused stale aggregate imports for `std.editor.extensions.host`,
`std.editor.services.debug_session`, and the absent `std.common.markdown.*`
compatibility paths.

The full legacy GUI system spec now runs far enough to execute examples, but it
is not a completed restart gate: `SIMPLE_LIB=src timeout 120s bin/simple test
test/03_system/editor_gui_spec.spl --mode=interpreter --clean --format json`
reported `32` passed and `48` failed. That broader legacy GUI suite remains
outside this focused TUI render fix.

2026-05-29 later GUI compatibility increment:

```text
SIMPLE_LIB=src bin/simple check src/lib/editor/render/md_renderer.spl src/lib/editor/view/preview_pane.spl src/lib/editor/view/preview_pane.spl test/03_system/editor_gui_spec.spl
PASS: All checks passed (4 files)

SIMPLE_LIB=src bin/simple check src/app/editor/main.spl test/03_system/editor_gui_spec.spl
PASS: All checks passed (2 files)

SIMPLE_LIB=src timeout 60s bin/simple test build/editor_gui_current_slices/editor_gui_74_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 180s bin/simple test test/03_system/editor_gui_spec.spl --mode=interpreter --clean --format json
PARTIAL: success=false, passed=51, failed=29
```

Changes in this increment:

- Restored the public Markdown renderer path as
  `src/lib/editor/render/md_renderer.spl` and imported it from both preview
  pane module paths, so public `std.editor.view.preview_pane` can resolve
  `md_render_blocks_for_tui_with_wiki`.
- Added `lsp_signature_popup_from_panel(...)` on both LSP popup module paths and
  mapped the active-parameter fallback to the existing `LspResultRow.command_name`
  field instead of the nonexistent `kind` field.
- Restored `ExtensionContext` subscription and workspace-state helpers used by
  `ExtensionHost`.
- Satisfied the legacy `--gui` source-contract slice without changing the
  startup-light editor readiness path.

Remaining failing legacy GUI slices after this increment are examples 20-37,
51, 53, 54, 57, 58, 60-63, 70, and 71. These are behavior failures in GUI
event routing, markdown/wiki commands, LSP hover/code-lens/inlay interactions,
table/property editing, and fold rendering; they remain open.

2026-05-29 parallel-agent follow-up:

```text
SIMPLE_LIB=src bin/simple check src/app/editor/editor_ctrl_core2.spl src/app/editor/gui_shell_core.spl src/app/editor/gui_shell_render.spl src/lib/editor/buffer/buffer.spl src/lib/editor/view/lsp_popup.spl src/lib/editor/view/lsp_popup.spl test/03_system/editor_gui_spec.spl
PASS: All checks passed (7 files)

SIMPLE_LIB=src timeout 180s bin/simple test test/03_system/editor_gui_spec.spl --mode=interpreter --clean --format json
PARTIAL: success=false, passed=51, failed=29
```

Parallel explorer findings were integrated for command routing and widget event
metadata: built-in GUI commands now run before generic external extension
dispatch, wiki rows and graph nodes expose `data-event`/`data-value` click
metadata, signature help uses `command_payload` for the active parameter, and
fold badge handling can remove a fold by start line. These changes compile, but
the aggregate legacy GUI count did not improve yet. A lower-level
`EditSession.open_file(...)` runtime path still fails in local probes with
`semantic: variable self not found` after JIT fallback, before GUI event
assertions can exercise the patched behavior. That session/runtime issue is the
next blocking slice for the editor GUI gate.

2026-05-29 session-open and link navigation increment:

```text
SIMPLE_LIB=src bin/simple check src/lib/editor/core/session.spl build/editor_session_open_probe.spl build/editor_open_file_probe.spl
PASS: All checks passed (3 files)

SIMPLE_LIB=src bin/simple run build/editor_session_open_probe.spl
PASS: probe printed before/after opened document path after interpreter fallback

SIMPLE_LIB=src timeout 60s bin/simple test build/editor_gui_current_slices/editor_gui_20_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 60s bin/simple test build/editor_gui_current_slices/editor_gui_21_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 180s bin/simple test test/03_system/editor_gui_spec.spl --mode=interpreter --clean --format json
PARTIAL: success=false, passed=58, failed=22
```

The `EditSession.open_file(...)` blocker was fixed by avoiding the nested
`me._bind_active_pane(...)` call and using a pure `editor_session_bind_panes`
helper that rebuilds the pane list. This avoids the interpreter self-writeback
failure and deep indexed field assignment. GUI link-click and ctrl-click routes
now install the resolved opened path into the shell state after the controller
reports `opened link:` or `created note:`. The legacy GUI suite improved from
`51/29` to `58/22` during this sequence; examples 20 and 21 now pass.

2026-05-29 GUI shell state-return increment:

```text
SIMPLE_LIB=src bin/simple check src/app/editor/editor_controller.spl src/app/editor/gui_shell_core.spl src/app/editor/gui_shell_render.spl src/app/editor/editor_ctrl_wiki.spl src/app/editor/editor_ctrl_core2.spl src/lib/editor/buffer/buffer.spl src/lib/editor/view/wiki_panel.spl src/lib/editor/view/wiki_panel.spl test/03_system/editor_gui_spec.spl
PASS: focused checks passed during the slice fixes

SIMPLE_LIB=src timeout 60s bin/simple test build/editor_gui_current_slices/editor_gui_22_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 60s bin/simple test build/editor_gui_current_slices/editor_gui_23_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 60s bin/simple test build/editor_gui_current_slices/editor_gui_24_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 60s bin/simple test build/editor_gui_current_slices/editor_gui_25_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 60s bin/simple test build/editor_gui_current_slices/editor_gui_27_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 60s bin/simple test build/editor_gui_current_slices/editor_gui_51_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 60s bin/simple test build/editor_gui_current_slices/editor_gui_71_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 180s bin/simple test test/03_system/editor_gui_spec.spl --mode=interpreter --clean --format json
PARTIAL: success=false, passed=65, failed=15
```

This increment fixed another set of GUI shell/controller writeback gaps by
making stateful task, vault search, quick switch, and template picker handlers
return or install the updated controller/session explicitly. It also aligned
the vault-search panel title with renderer controls, guarded empty Markdown
stats in GUI status rendering, added missing wiki-panel target helpers, and
made headless visible-line lookup skip folded ranges. Remaining failures are
now concentrated in attachment picker, Problems/LSP panels, LSP navigation and
code-lens/hover state, property/table edit writeback, and a vault-property
string contains issue.

2026-05-29 picker/diagnostics/property/table increment:

```text
SIMPLE_LIB=src timeout 60s src/compiler_rust/target/debug/simple test build/editor_gui_current_slices/editor_gui_28_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 60s src/compiler_rust/target/debug/simple test build/editor_gui_current_slices/editor_gui_29_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 60s src/compiler_rust/target/debug/simple test build/editor_gui_current_slices/editor_gui_60_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 60s src/compiler_rust/target/debug/simple test build/editor_gui_current_slices/editor_gui_61_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 80s src/compiler_rust/target/debug/simple test build/editor_gui_current_slices/editor_gui_62_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 60s src/compiler_rust/target/debug/simple test build/editor_gui_current_slices/editor_gui_63_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 180s src/compiler_rust/target/debug/simple test test/03_system/editor_gui_spec.spl --mode=interpreter --clean --format json
PARTIAL: success=false, passed=71, failed=9
```

This increment completed the remaining non-LSP GUI shell state-return cluster:
attachment picker, Problems filtering/grouping/sorting, wiki property submit,
vault property submit/review, and Markdown table row/column/cell edits. It also
fixed the interpreter nested string method gap for `contains`, `starts_with`,
`ends_with`, and `index_of`, which exposed and then unblocked the property
assertions under interpreter fallback. Remaining failures are now concentrated
in the LSP result/history/outline/hover/code-lens cluster and workspace-edit
preview controls.

2026-05-29 LSP panel partial increment:

```text
SIMPLE_LIB=src timeout 60s src/compiler_rust/target/debug/simple test build/editor_gui_current_slices/editor_gui_33_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 60s src/compiler_rust/target/debug/simple test build/editor_gui_current_slices/editor_gui_34_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 60s src/compiler_rust/target/debug/simple test build/editor_gui_current_slices/editor_gui_35_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 60s src/compiler_rust/target/debug/simple test build/editor_gui_current_slices/editor_gui_36_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 180s src/compiler_rust/target/debug/simple test test/03_system/editor_gui_spec.spl --mode=interpreter --clean --format json
PARTIAL: success=false, passed=75, failed=5
```

This increment hydrated LSP result panels from simple LSP JSON for reference,
document-symbol, and code-lens rows; rendered LSP result rows from `panel.rows`
instead of title/empty-state display lines; added outline rendering; switched
document-symbol outline application to the existing `OutlineItem` model; added
nested `to_i64` string dispatch for interpreter fallback; and made GUI
`lsp-back` pop/open/focus through shell state. Remaining editor GUI failures at
this point were examples 30, 31, 37, 54, and 57: workspace-edit preview
controls, rename preview conflict rendering, code-action group/filter dispatch,
delayed hover startup state, and inline code-lens debug command state.

2026-05-29 editor GUI closure increment:

```text
SIMPLE_LIB=src timeout 60s src/compiler_rust/target/debug/simple test build/editor_gui_current_slices/editor_gui_30_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 60s src/compiler_rust/target/debug/simple test build/editor_gui_current_slices/editor_gui_31_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 60s src/compiler_rust/target/debug/simple test build/editor_gui_current_slices/editor_gui_37_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 60s src/compiler_rust/target/debug/simple test build/editor_gui_current_slices/editor_gui_54_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 60s src/compiler_rust/target/debug/simple test build/editor_gui_current_slices/editor_gui_57_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=1, failed=0

SIMPLE_LIB=src timeout 180s src/compiler_rust/target/debug/simple test test/03_system/editor_gui_spec.spl --mode=interpreter --clean --format json
PASS: success=true, passed=80, failed=0
```

This increment completed the remaining editor GUI shell gate. Workspace-edit
preview rows are hydrated for formatting and rename previews, direct controller
preview methods now write the populated LSP panel and conflict state back to the
controller, GUI code-action filter/group events update the panel state, delayed
hover events hydrate the hover panel/popup after the configured threshold, and
inline code-lens debug commands update the shell controller state.

## Remaining Scope Boundaries

- No dedicated `editor_tui_render_completion` plan exists; this note is the
  merged parallel TUI/editor slice for the GUI renderer restart.
- `test/03_system/editor_gui_spec.spl` now passes `80/80` under the focused
  interpreter invocation used by this restart lane.
- Split-border rendering is now present for the current fallback adjacent-rect
  layout. Full recursive `SplitTree` ratio-driven geometry remains dependent
  on the broader editor split-tree/layout work and is not claimed complete by
  this focused restart.
