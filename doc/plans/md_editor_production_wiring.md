# Plan: Production-Level Markdown Editor Wiring

## Status: IMPLEMENTATION COMPLETE — compiled UI smoke remains

## Context

The editor library (`src/lib/editor/`, ~65K LOC, 55 files) has comprehensive markdown support — piece table, preview pane, block model, md renderer, md commands (13.9K LOC), md edit assist (9.4K), md diagnostics (20.9K), command palette (4.6K), md vim motions, md folding, outline panel, md search, lsp client — but the app layer (`src/app/editor/editor_controller.spl`, 347 LOC) references **none** of it. This plan wires the library into the running editor.

A markdown parser library also exists at `src/lib/common/markdown/` (1,684 LOC) with `parse_blocks_with_ranges()`, inline parsing, and block-level rendering.

## Latent Bug — NOT A BUG

`md_renderer.spl:27` references `block.content` — verified `RenderBlock` in `block_model.spl` DOES have `content: text` field. No fix needed.

---

## Phase 1: MdEditorState on EditorDocument — DONE

**Files:** `src/lib/editor/20.core/document.spl`

- [x] Added `md_state: MdEditorState` and `cached_md_stats: MdDocStats` fields to `EditorDocument`
- [x] On file open: if `language_id == "markdown"`, initializes via `md_editor_state_new()` + `md_compute_stats()`
- Cross-layer: layer 20 references types from layers 50/60. Parses clean in interpreter. **Compiled-mode verification pending.**

## Phase 2: Enter/Tab Smart Editing Intercepts — DONE

**File:** `src/app/editor/editor_controller.spl`

- [x] In `_dispatch_insert_key`: markdown check before `ctrl_handle_insert_key`
- [x] Enter: calls `md_assist_on_enter(current_line, cursor_col)`
- [x] Tab: calls `md_assist_on_tab(current_line, cursor_col)`

## Phase 3: MdCommandResult Glue Dispatcher — DONE

**New file:** `src/app/editor/md_dispatch.spl` (59 lines)

- [x] `md_apply_result(buffer, result)` — MdCommandResult → EditorBuffer mutations
- [x] `md_buffer_content(buffer) -> text` — full content extraction
- [x] `md_dispatch_motion(prefix, key, content, cursor_line, cursor_col) -> MdMotionResult`
- [x] `md_update_preview(doc, buffer)` — preview pane content + scroll sync

## Phase 4: Command Palette (Ctrl+P) — DONE

**Files:** `src/app/editor/editor_controller.spl`, `src/app/editor/commands.spl`

- [x] `palette_state: PaletteState` field on EditorController
- [x] `_dispatch_palette_key`: Esc/Enter/Up/Down/typing
- [x] `_open_palette`: merges `editor_all_commands()` + `md_commands_palette_entries()` for .md
- [x] `_execute_palette_command`: routes `"markdown.*"` to `md_commands_dispatch` + `md_apply_result`
- [x] Ctrl+P trigger in normal mode
- [x] `:palette` command alias

## Phase 5: Live Preview Pane (Right Dock) — DONE

**Files:** `src/app/editor/tui_shell.spl`, `src/app/editor/editor_controller.spl`

- [x] Right dock zone rendering with `preview_pane_render()`
- [x] `ctrl_compute_zones` subtracts `right_w` from editor width
- [x] Insert-mode keystroke updates preview via `md_update_preview`
- [x] Toggle: Ctrl+Shift+V / `:preview` / command palette

## Phase 6: Outline Panel — DONE

**File:** `src/app/editor/tui_shell.spl`

- [x] Right dock zone rendering with `outline_panel_render()`
- [x] Toggle: Ctrl+Shift+O / `:outline` / command palette

## Phase 7: Status Bar with Markdown Stats — DONE

**Files:** `src/app/editor/tui_shell.spl`, `src/app/editor/commands.spl`

- [x] Status bar appends `md_stats_to_status_bar(doc.cached_md_stats)` for .md files
- [x] Stats recomputed on save only

## Phase 8: Diagnostics on Save — DONE

**File:** `src/app/editor/commands.spl`

- [x] Save handler calls `md_diagnose(content, path)` for markdown
- [x] Recomputes `cached_md_stats` on save

## Phase 9: Vim Markdown Motions (Normal Mode) — DONE

**File:** `src/app/editor/editor_controller.spl`

- [x] `]`/`[` prefix → `md_dispatch_motion` for markdown files
- [x] `g` prefix → `gx` open link for markdown files
- [x] Non-markdown files keep existing `g` = go-to-top behavior

## Phase 10: GUI Shell Wiring — DONE

**File:** `src/app/editor/gui_shell.spl`

- [x] Ctrl+P → `_open_palette()`
- [x] Ctrl+Shift+V → preview toggle
- [x] Ctrl+Shift+O → outline toggle
- [x] Ctrl+S → md stats recomputation
- [x] Frame rendering: preview/outline HTML in right panel, md stats in status bar

## Phase 11: End-to-End Tests — DONE

**Files:** `test/system/editor_markdown_spec.spl` (extended), `test/system/editor_palette_spec.spl`

- [x] 65 structural wiring tests, all passing
- [x] Fixed 5 pre-existing block kind tests (were grepping wrong file — `block_model.spl` → `adapter.spl`/`parse.spl`)
- [x] `test/system/editor_palette_spec.spl` created for dedicated palette service, routing, and Markdown command coverage

---

## Execution Order

| # | Phase | Depends On | Risk |
|---|-------|-----------|------|
| 0 | Fix block.content bug in md_renderer.spl | None | Low |
| 1 | MdEditorState on EditorDocument | None | Low (circular dep risk) |
| 2 | Enter/Tab intercepts | Phase 1 | Low |
| 3 | md_dispatch.spl glue | Phase 1 | Low (new file) |
| 4 | Command palette | Phases 1, 3 | Medium |
| 5 | Preview pane TUI | Phases 1, 3 | Medium (layout math) |
| 6 | Outline panel | Phase 5 | Low (same pattern) |
| 7 | Status bar stats | Phase 1 | Low |
| 8 | Diagnostics on save | Phases 1, 3 | Low |
| 9 | Vim motions | Phase 3 | Medium (prefix conflicts) |
| 10 | GUI shell | Phases 4-8 | Low (mirrors TUI) |
| 11 | E2E tests | All | Low |

## Critical Files

| File | Action |
|------|--------|
| `src/lib/editor/20.core/document.spl` | Add md_state, cached_md_stats fields |
| `src/app/editor/editor_controller.spl` | Add palette_state, Enter/Tab intercept, palette dispatch, vim motion prefix |
| `src/app/editor/md_dispatch.spl` | **NEW** — MdCommandResult→buffer glue, motion dispatch |
| `src/app/editor/tui_shell.spl` | Preview/outline rendering, right dock layout, status bar stats |
| `src/app/editor/commands.spl` | Merge md palette entries, diagnostics-on-save, palette command |
| `src/app/editor/gui_shell.spl` | Mirror TUI wiring for GUI mode |
| `src/lib/editor/40.render/md_renderer.spl` | Fix block.content bug |
| `test/system/editor_markdown_spec.spl` | Extend with wiring verification tests |
| `test/system/editor_palette_spec.spl` | Dedicated palette service, routing, and Markdown command tests |

## Reusable Existing Functions

| Function | File | Used In |
|----------|------|---------|
| `md_assist_on_enter(line, col)` | `50.extensions/builtin/md_edit_assist.spl` | Phase 2 |
| `md_assist_on_tab(line, col)` | `50.extensions/builtin/md_edit_assist.spl` | Phase 2 |
| `md_commands_dispatch(cmd, state, content)` | `50.extensions/builtin/md_commands.spl` | Phase 4 |
| `md_commands_palette_entries()` | `50.extensions/builtin/md_commands.spl` | Phase 4 |
| `preview_pane_create/update/render/sync_scroll` | `30.view/preview_pane.spl` | Phase 5 |
| `md_render_blocks_for_tui(model, start, h)` | `40.render/md_renderer.spl` | Phase 5 |
| `BlockModel.from_markdown(content)` | `40.render/block_model.spl` | Phase 5 |
| `outline_panel_render(panel, h)` | `30.view/outline_panel.spl` | Phase 6 |
| `md_compute_stats(content)` | `60.services/md_doc_stats.spl` | Phase 7 |
| `md_diagnose(content, path)` | `60.services/md_diagnostics.spl` | Phase 8 |
| `md_vim_next_heading` etc. | `50.extensions/builtin/md_vim_motions.spl` | Phase 9 |
| `palette_new/show/hide/select_*` | `60.services/command_palette.spl` | Phase 4 |

## Verification

1. ~~`bin/simple run src/app/editor/main.spl test.md` — editor launches, opens .md file~~ — requires compiled mode (`rt_args` extern), cannot test in interpreter
2. Type in insert mode → Enter auto-continues lists — **WIRED, needs compiled-mode test**
3. Ctrl+P opens command palette with markdown commands — **WIRED, needs compiled-mode test**
4. Ctrl+Shift+V toggles preview pane with rendered markdown — **WIRED, needs compiled-mode test**
5. `]]` / `[[` in normal mode jumps between headings — **WIRED, needs compiled-mode test**
6. Status bar shows word count for .md files — **WIRED, needs compiled-mode test**
7. `:w` saves and runs diagnostics — **WIRED, needs compiled-mode test**
8. `bin/simple test test/system/editor_markdown_spec.spl` — **65/65 PASS**
9. `bin/simple test test/system/editor_palette_spec.spl` — dedicated palette structure and wiring spec

---

## What's Left

### Must-do (compile blockers / correctness)

1. **Cross-layer compile verification** — `document.spl` (layer 20) imports `MdEditorState` (layer 50) and `md_compute_stats` (layer 60). Parses clean in interpreter but needs `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` to verify compiled mode. If it fails, extract `MdEditorState`/`MdDocStats` struct defs to `src/lib/editor/20.core/md_state.spl`.

2. **Compiled-mode UI launch test** — Editor requires `rt_args` extern (compiled only). After bootstrap, run `bin/simple run src/app/editor/main.spl test.md` and verify: file opens, Enter continues lists, Ctrl+P shows palette, Ctrl+Shift+V shows preview, status bar shows word count.

### Nice-to-have (non-blocking)

3. **Extension host cleanup** — `gui_shell.spl` still calls `extension_host.activate("markdown-language")` and `extension_host.activate("simple-language")`. Keep it unless ExtensionHost ownership changes; the Markdown language service activation matches the editor's IDE-style language infrastructure.
