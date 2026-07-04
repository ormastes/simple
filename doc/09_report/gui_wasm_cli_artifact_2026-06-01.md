# GUI WASM CLI Artifact Evidence

- status: pass
- reason: pass

## Artifacts

### hello
- status: pass
- reason: pass
- source: examples/06_io/ui/hello_wasm_gui.spl
- output: build/gui_wasm_cli_artifact/hello_wasm_gui.wasm
- size bytes: 4380
- magic hex: 0061736d
- version hex: 01000000
- import count: 0
- imports: none

### widget_matrix
- status: pass
- reason: pass
- source: examples/06_io/ui/widget_matrix_wasm_gui.spl
- output: build/gui_wasm_cli_artifact/widget_matrix_wasm_gui.wasm
- size bytes: 15028
- magic hex: 0061736d
- version hex: 01000000
- import count: 0
- imports: none
- marker coverage: checkbox, dropdown/select transitions, text input/textfield, textarea, tabs, dialog open/close, table/list selection, progress validation, image load/error/tooltip, tree/scroll, menu hierarchy, statusbar update/queue, and supported menu-command/event response strings; this does not claim command-bar coverage for the widget matrix
- event markers: matrix_checkbox:changed, matrix_dropdown:changed, matrix_dropdown:beta-selected, matrix_textfield:accepted, matrix_textarea:accepted, matrix_tabs:selected, matrix_dialog:opened, matrix_dialog:closed, matrix_table:selected, matrix_table:row-primary-selected, matrix_list:selected, matrix_progress:changed, matrix_progress:clamped, matrix_tooltip:shown, matrix_image:loaded, matrix_image:error, matrix_scroll:accepted, matrix_menu:accepted, matrix_menu:view-accepted, matrix_menu:zoom-accepted, matrix_statusbar:updated, matrix_statusbar:queued, matrix_event:ignored

### builder_matrix
- status: pass
- reason: pass
- source: examples/06_io/ui/builder_matrix_wasm_gui.spl
- output: build/gui_wasm_cli_artifact/builder_matrix_wasm_gui.wasm
- size bytes: 9486
- magic hex: 0061736d
- version hex: 01000000
- import count: 0
- imports: none
- marker coverage: real common.ui builder imports and builder_matrix_tree construction, radio, switch, search_bar, segmented_control, navigation_bar, tab_bar, card, heading, label, divider, command_palette, sidebar, inspector, scroll, textarea, tree/treenode, glass_title_bar, command_bar, workspace_tabs, toast, sheet_modal, context_menu, utility_rail, status_chip, selection_pill, empty_state, and supported builder event response strings
- event markers: builder_radio:changed, builder_switch:toggled, builder_search:accepted, builder_segmented:changed, builder_command_palette:accepted, builder_sheet_modal:opened, builder_context_menu:opened, builder_event:ignored

## Compiler Output

### builder_matrix.compile.out
- Compiled examples/06_io/ui/builder_matrix_wasm_gui.spl -> build/gui_wasm_cli_artifact/builder_matrix_wasm_gui.wasm

### hello.compile.out
- Compiled examples/06_io/ui/hello_wasm_gui.spl -> build/gui_wasm_cli_artifact/hello_wasm_gui.wasm

### widget_matrix.compile.out
- Compiled examples/06_io/ui/widget_matrix_wasm_gui.spl -> build/gui_wasm_cli_artifact/widget_matrix_wasm_gui.wasm

## Compiler Error

### builder_matrix.compile.err

### hello.compile.err

### widget_matrix.compile.err
