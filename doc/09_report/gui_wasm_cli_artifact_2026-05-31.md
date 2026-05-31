# GUI WASM CLI Artifact Evidence

- status: pass
- reason: pass

## Artifacts

### hello
- status: pass
- reason: pass
- source: examples/ui/hello_wasm_gui.spl
- output: build/gui_wasm_cli_artifact/hello_wasm_gui.wasm
- size bytes: 2787
- magic hex: 0061736d
- version hex: 01000000

### widget_matrix
- status: pass
- reason: pass
- source: examples/ui/widget_matrix_wasm_gui.spl
- output: build/gui_wasm_cli_artifact/widget_matrix_wasm_gui.wasm
- size bytes: 4521
- magic hex: 0061736d
- version hex: 01000000
- marker coverage: checkbox, dropdown/select, text input/textfield, textarea, tabs, dialog, table/list, progress, image, tooltip, tree/scroll, menu, statusbar, and supported menu-command/event response strings; this does not claim command-bar coverage for the widget matrix
- event markers: matrix_checkbox:changed, matrix_dropdown:changed, matrix_textfield:accepted, matrix_textarea:accepted, matrix_tabs:selected, matrix_dialog:opened, matrix_scroll:accepted, matrix_menu:accepted, matrix_event:ignored

### builder_matrix
- status: pass
- reason: pass
- source: examples/ui/builder_matrix_wasm_gui.spl
- output: build/gui_wasm_cli_artifact/builder_matrix_wasm_gui.wasm
- size bytes: 7424
- magic hex: 0061736d
- version hex: 01000000
- marker coverage: real common.ui builder imports and builder_matrix_tree construction, radio, switch, search_bar, segmented_control, navigation_bar, tab_bar, card, heading, label, divider, command_palette, sidebar, inspector, scroll, textarea, tree/treenode, glass_title_bar, command_bar, workspace_tabs, toast, sheet_modal, context_menu, utility_rail, status_chip, selection_pill, empty_state, and supported builder event response strings
- event markers: builder_radio:changed, builder_switch:toggled, builder_search:accepted, builder_segmented:changed, builder_command_palette:accepted, builder_sheet_modal:opened, builder_context_menu:opened, builder_event:ignored

## Compiler Output

### builder_matrix.compile.out
- Compiled examples/ui/builder_matrix_wasm_gui.spl -> build/gui_wasm_cli_artifact/builder_matrix_wasm_gui.wasm

### hello.compile.out
- Compiled examples/ui/hello_wasm_gui.spl -> build/gui_wasm_cli_artifact/hello_wasm_gui.wasm

### widget_matrix.compile.out
- Compiled examples/ui/widget_matrix_wasm_gui.spl -> build/gui_wasm_cli_artifact/widget_matrix_wasm_gui.wasm

## Compiler Error

### builder_matrix.compile.err

### hello.compile.err

### widget_matrix.compile.err
