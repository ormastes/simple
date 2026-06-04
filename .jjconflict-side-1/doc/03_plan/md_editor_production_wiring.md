# Plan: Production-Level Markdown Editor Wiring

## Status: IMPLEMENTATION COMPLETE — runtime UI smoke remains

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
- Cross-layer: layer 20 references types from layers 50/60. Parses clean in interpreter and passes scoped native-build lowering. Real runtime launch still needs non-stubbed editor externs.

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
- [x] GUI source area now renders as an editable source surface with `contenteditable`, textbox role, language metadata, active-line metadata, and cursor marker
- [x] GUI startup registers built-in Simple and Markdown extension manifests before activating them
- [x] Extension host supports activation-event routing for `*`, `onLanguage:*`, and `onCommand:*`; GUI file open routes active document language into the extension host
- [x] EditorController owns the extension host, initializes built-ins once, and routes registered Markdown palette commands through extension metadata before dispatching Markdown command handlers
- [x] Extension host can discover external `extension.sdn` manifests from configured roots without executing extension code
- [x] EditorController startup indexes workspace/user/system extension roots plus `SIMPLE_EDITOR_EXTENSION_PATH`
- [x] Extension host creates and cleans up `ExtensionContext` records on activate/deactivate, giving plugins lifecycle-backed API context state before executable runtime support
- [x] Extension host records editor events and matches them against extension subscriptions; controller and GUI file-open/command paths emit language, document-open, and command lifecycle events
- [x] Extension contexts now carry workspace state with host-level get/set helpers
- [x] External registered commands now dispatch to a host-owned pending invocation queue instead of failing as “not executable”; actual execution remains behind runtime/sandbox implementation
- [x] Extension host now has an explicit default-deny runtime policy, allowed-root checks, and a drain step that marks pending invocations as blocked, sandbox-ready, or external-process-ready without executing untrusted code
- [x] `--gui-sdl` mode runs the GUI shell through the SDL bridge, presents frames, and polls runtime SDL events
- [x] SDL key events map Escape/Enter/Backspace/Tab and printable ASCII into `GuiEvent(kind: "key", data: ...)` for controller dispatch
- [x] SDL text input events map into `GuiEvent(kind: "text", ...)` and are dispatched character-by-character through `EditorController`
- [x] SDL Ctrl/Ctrl+Shift key chords map to GUI command names, including GUI clipboard copy/paste and preview shortcut routing
- [x] SDL window resize/focus/blur events map into GUI events so the shell can update layout dimensions and focus status

## Phase 11: End-to-End Tests — DONE

**Files:** `test/03_system/editor_markdown_spec.spl` (extended), `test/03_system/editor_palette_spec.spl`

- [x] 67 structural wiring tests, all passing
- [x] Fixed 5 pre-existing block kind tests (were grepping wrong file — `block_model.spl` → `adapter.spl`/`parse.spl`)
- [x] `test/03_system/editor_palette_spec.spl` created for dedicated palette service, routing, and Markdown command coverage
- [x] `test/03_system/editor_gui_sdl_spec.spl` covers SDL bridge declarations, key/chord/text-input/window-event mapping, shell run-loop wiring, clipboard shortcuts, and `--gui-sdl`

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
| `src/lib/editor/render/md_renderer.spl` | Fix block.content bug |
| `test/03_system/editor_markdown_spec.spl` | Extend with wiring verification tests |
| `test/03_system/editor_palette_spec.spl` | Dedicated palette service, routing, and Markdown command tests |

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
8. `bin/simple test test/03_system/editor_markdown_spec.spl` — **67/67 PASS**
9. `bin/simple test test/03_system/editor_palette_spec.spl` — **11/11 PASS**
10. `bin/simple check src/app/editor/main.spl --source src` — **PASS**
11. `bin/simple check src/app/editor/gui_shell.spl --source src` — **PASS**
12. `bin/simple check src/lib/editor/70.backend/gui_sdl_bridge.spl` — **PASS**
13. `bin/simple test test/03_system/editor_gui_spec.spl` — **31/31 PASS**
14. `bin/simple test test/03_system/editor_gui_sdl_spec.spl` — **18/18 PASS**
15. `bin/simple test test/03_system/editor_extension_spec.spl` — **27/27 PASS**
16. `bin/simple native-build --source src/app --source src/lib --entry src/app/editor/main.spl --entry-closure --output build/editor-main-smoke` — links, but stubs `rt_args`, `EditSession_dot_new`, `editor_tui_run`, and `gui_shell_run`; linker smoke only, not behavior evidence
17. `scripts/bootstrap/bootstrap-from-scratch.sh --deploy --no-mcp` — attempted 2026-05-12; blocked in `rust-seed-build` by signal 15 during Cargo compilation, before deploy

---

## Reality Check: Obsidian-like GUI and VS Code-like Plugins

### GUI edit parity

The editor is not yet a full Obsidian-like GUI editor. It now has Markdown-aware editing services, live preview/outline wiring, an editable HTML source surface, and a `--gui-sdl` runtime loop that presents frames and polls SDL key, chord, text-input, mouse, resize, focus, blur, and close events. The default HTML-presenter path still has `gui_shell_poll_event()` returning no events. True GUI edit parity still needs:

- selection and composition events beyond the current SDL key/chord/text/mouse/window mapping
- richer mapping from GUI edit events back into `EditorController`/`EditorBuffer`
- selection/caret synchronization between rendered source, buffer, and viewport
- runtime smoke test that launches GUI mode and verifies edit → preview/stat updates

### Plugin parity

The editor is not yet VS Code-level plugin support. It has SDN manifests, commands/languages/keybinding contribution registries, built-in manifest registration, startup external manifest discovery, activation/deactivation, lifecycle-backed extension contexts, workspace state, editor event/subscription routing, activation-event routing, contribution lookup, registered-command dispatch for built-in Markdown commands, pending runtime invocation queueing for external commands, and an explicit default-deny runtime policy with allowed-root and sandbox/external-process readiness states. Remaining VS Code-like infrastructure:

- actual sandbox runner that executes extension `main` modules through `ExtensionContext`
- external-process runner only if explicitly allowed by policy

## What's Left

### Must-do (compile blockers / correctness)

1. **Entry-closure import hygiene** — DONE for the editor entrypoint. `src/app/editor/main.spl` now imports `EditSession`, `editor_tui_run`, and `gui_shell_run` explicitly, and `bin/simple check src/app/editor/main.spl --source src` passes.

2. **Compiled-mode UI launch test** — Editor requires non-stubbed runtime externs. After import hygiene and real runtime extern resolution, run `bin/simple run src/app/editor/main.spl --gui-sdl test.md` and verify: file opens, SDL typing reaches the controller, Enter continues lists, Ctrl+P shows palette, Ctrl+Shift+V shows preview, status bar shows word count. The 2026-05-12 bootstrap/deploy attempt was terminated by signal 15 while compiling the Rust seed compiler/runtime.

### Nice-to-have (non-blocking)

3. **Default GUI event pump** — Keep `--gui-sdl` as the runtime-backed GUI path, or replace the empty default `gui_shell_poll_event()` placeholder with a browser/native event source. Add a compiled-mode GUI smoke test that proves typing, caret movement, selection, save, preview toggle, and outline toggle work through the GUI path.

4. **Plugin runtime activation** — DONE up to the safe boundary. `ExtensionCommandInvocation` records now drain through a default-deny runtime policy and produce blocked/sandbox-ready/external-process-ready dispatch records. Actual execution of extension `main` modules still requires implementing the sandbox runner.
