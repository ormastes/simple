# Plan: Editor Markdown Editing Subsystem

- **Date:** 2026-05-30
- **Status:** Planned
- **Priority:** P1
- **FR:** `doc/08_tracking/feature_request/editor_markdown_editing_subsystem_2026-05-28.md`
- **Effort:** XL (4-6 weeks across phases)

## Context

The editor TUI/GUI shell was wired against a markdown-editing subsystem that was
never fully implemented. Production wiring (Phase 1-8 in
`doc/03_plan/md_editor_production_wiring.md`) is complete, and minimal stubs
were added to compile a basic frame. The core types exist as stubs:
- `MdEditorState`, `MdMotionResult`, `MdCommandResult`, `md_commands_dispatch`
  in `src/lib/editor/view/md_editing.spl` (minimal implementations)
- `RenderBlock` in `src/lib/editor/render/block_model.spl` (stub)
- `md_table_next_cell`, `md_dispatch_motion` in `md_editing.spl` (partial)

The stubs are insufficient for real editing. Three controller files
(`editor_ctrl_core`, `editor_ctrl_core2`, `editor_ctrl_wiki`) and
`tui_shell_panels.spl` need the full subsystem with richer block model,
complete vim bindings, table/callout editing, and stdlib gaps (`str.slice`,
`discover_extensions`).

## Prerequisites and Blockers

1. **EditorBuffer API** -- landed 2026-05-28 (no blocker)
2. **`str.slice` stdlib method** -- must be implemented or shimmed in
   `src/lib/common/text/` or runtime; needed by motion/selection logic
3. **`discover_extensions` runtime** -- plugin host enumeration; needed by
   `editor_extension_roots.spl`
4. **HIR type inference** -- existing controllers compile once the types exist
   (no compiler FR needed)

## Phased Implementation Steps

### Phase 1: Core Types and Block Model (S)

Extend existing stubs into full implementations.

1. Extend `src/lib/editor/render/block_model.spl` -- the stub defines
   `struct RenderBlock`; add variants (heading, paragraph, code, list, table,
   callout, hr, blank), add `BlockModel` (list of `RenderBlock` with
   line-mapping), add `block_model_from_lines(lines: List<String>) -> BlockModel`
2. Extend `src/lib/editor/view/md_editing.spl` -- the stub defines
   `MdEditorState`, `MdMotionResult`, `MdCommandResult` with minimal fields;
   enrich `MdEditorState` to wrap `EditorDocument`, `BlockModel`, cursor
   position, selection, mode (normal/insert/visual), undo stack ref; enrich
   `MdMotionResult` with selection_range; enrich `MdCommandResult` with
   edited_lines, new_cursor, needs_reparse
3. Wire `__init__.spl` re-exports so `use std.editor.core` exposes all types

**Files to modify:** `src/lib/editor/render/block_model.spl` (extend stub),
`src/lib/editor/view/md_editing.spl` (extend stubs),
`src/lib/editor/render/md_renderer.spl` (import block_model),
existing `__init__.spl` files

### Phase 2: Command Dispatch (M)

Wire the command-result pipeline that controllers call.

1. Extend `src/lib/editor/view/md_editing.spl` `md_commands_dispatch` -- currently
   a minimal stub; expand to full command routing with sub-handlers. Also extend
   `src/app/editor/md_dispatch.spl` for app-level dispatch wiring
2. Implement enter-key smart editing (auto-continue lists, indent code blocks)
3. Implement tab/shift-tab indent/outdent for list items and code
4. Implement delete-line, duplicate-line, move-line-up/down
5. Wire into `editor_ctrl_core.spl` and `editor_ctrl_core2.spl` replacing stubs

**Files to modify:** `src/lib/editor/view/md_editing.spl` (extend dispatch),
`src/app/editor/md_dispatch.spl` (extend),
`src/app/editor/editor_ctrl_core.spl`, `src/app/editor/editor_ctrl_core2.spl`

### Phase 3: Motions and Vim Bindings (L)

Implement cursor motion primitives and vim-mode overlay.

1. Implement `src/lib/editor/extensions/builtin/md_vim_motions.spl` --
   word/WORD motion, paragraph motion, heading motion (jump to next/prev `#`),
   sentence motion, `gg`/`G`, `0`/`$`/`^`
2. Each motion returns `MdMotionResult` with optional selection
3. Implement `src/lib/editor/extensions/vim_mode.spl` -- modal state machine
   (Normal, Insert, Visual, VisualLine, Command), keymap dispatch per mode,
   operator-pending (d, c, y) + motion composition, repeat with `.`
4. Implement search motions (`/`, `?`, `n`, `N`) using existing `md_search.spl`

**Files to modify:** `src/lib/editor/extensions/builtin/md_vim_motions.spl`,
`src/lib/editor/extensions/vim_mode.spl`

### Phase 4: Tables (M)

Implement GFM-compatible table editing.

1. Create `src/lib/editor/extensions/builtin/md_table_ops.spl` --
   `md_table_parse(lines: List<String>, row: Int) -> MdTable?` detecting
   pipe-delimited table blocks
2. `md_table_add_row`, `md_table_delete_row`, `md_table_add_col`,
   `md_table_delete_col`, `md_table_align_col(col, align)`
3. Tab navigation within cells (Tab = next cell, Shift+Tab = prev cell)
4. Auto-format: re-pad columns to equal width on save/leave
5. Wire into command dispatch as `table.*` commands

**Files to create:** `src/lib/editor/extensions/builtin/md_table_ops.spl`
**Files to modify:** `src/app/editor/md_dispatch.spl`

### Phase 5: Callouts (S)

1. Create `src/lib/editor/extensions/builtin/md_callout_ops.spl` --
   parse `> [!TYPE]` blocks (note, warning, tip, important, caution),
   `md_callout_insert(type: String) -> MdCommandResult`,
   `md_callout_toggle_fold`, `md_callout_change_type`
2. Syntax highlight support in `block_model.spl` -- `RenderBlock.Callout`
   variant with type and fold state
3. Wire into command dispatch as `callout.*` commands

**Files to create:** `src/lib/editor/extensions/builtin/md_callout_ops.spl`
**Files to modify:** `src/lib/editor/render/block_model.spl`,
`src/app/editor/md_dispatch.spl`

### Phase 6: Stdlib Gaps (S)

1. Implement `str.slice(start, end) -> String` in
   `src/lib/common/text/` (or as a runtime extern `rt_string_slice`)
2. Implement `discover_extensions(path: String) -> List<ExtensionManifest>`
   in `src/lib/editor/extensions/roots.spl`
3. Verify all three controller files compile with `bin/simple check`

**Files to modify:** `src/lib/common/text/` (new method or file),
`src/lib/editor/extensions/roots.spl`

### Phase 7: Integration and Tests (M)

1. Create `test/01_unit/lib/editor/md_block_model_spec.spl` -- heading/para/code/list/table/callout parsing
2. Create `test/01_unit/lib/editor/md_command_dispatch_spec.spl` -- enter, tab, delete commands
3. Create `test/01_unit/lib/editor/md_vim_motions_spec.spl` -- word, heading, paragraph motions
4. Create `test/01_unit/lib/editor/md_table_ops_spec.spl` -- add/delete row/col, align, tab-nav
5. End-to-end: `bin/simple check src/app/editor/` passes with zero HIR failures

**Files to create:** `test/01_unit/lib/editor/md_block_model_spec.spl`,
`test/01_unit/lib/editor/md_command_dispatch_spec.spl`,
`test/01_unit/lib/editor/md_vim_motions_spec.spl`,
`test/01_unit/lib/editor/md_table_ops_spec.spl`

## Acceptance Criteria

- [ ] `MdEditorState`, `MdMotionResult`, `MdCommandResult` types exist and compile
- [ ] `md_commands_dispatch` routes at least 10 commands (enter, tab, shift-tab,
      delete-line, duplicate-line, move-up, move-down, heading-toggle, bold, italic)
- [ ] Vim motions: w, b, e, W, B, E, 0, $, ^, gg, G, {, }, [[, ]] all produce
      correct `MdMotionResult`
- [ ] Table editing: add/delete row/col, tab navigation, auto-format
- [ ] Callout insert/fold/change-type
- [ ] `str.slice` works in interpreter mode
- [ ] `discover_extensions` returns manifests from a scan directory
- [ ] `bin/simple check src/app/editor/` passes with zero HIR type-inference failures
- [ ] All spec files pass in interpreter mode

## Risk Factors

- **Vim mode complexity (High):** Operator-pending + repeat (`.`) is substantial;
  consider shipping Phase 3 as "basic motions" first, defer operator composition
  to a follow-up
- **`str.slice` runtime interaction (Medium):** If implemented as pure Simple,
  must handle UTF-8 correctly; if extern, needs `rt_string_slice` in runtime.c
- **Block model re-parse performance (Low):** Full re-parse on every keystroke
  may lag on large documents; incremental update can be deferred
- **Controller coupling (Medium):** The three controller files may have additional
  unresolved types beyond what the FR lists; Phase 1 compilation check will
  surface these early
