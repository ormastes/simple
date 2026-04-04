# Examples Check

## examples/ui

- Total: `28`
- Ok: `9`
- Error: `17`
- Timeout: `2`
- Crash: `0`

### Failures

- `examples/ui/demo_async.spl` `error` code=1 DEBUG: cannot modify self in file: examples/ui/demo_async.spl, assignment: self.values[...]
- `examples/ui/demo_button_checkbox_dropdown.spl` `error` code=1 PASS: tree built with 10 widgets
- `examples/ui/demo_input_textfield.spl` `error` code=1 error: semantic: undefined field: unknown property or method 'id' on String
- `examples/ui/demo_menu_tooltip.spl` `error` code=1 PASS: tree built with 14 widgets
- `examples/ui/demo_menubar_statusbar.spl` `error` code=1 error: semantic: variable `app` not found
- `examples/ui/demo_panel_text_divider.spl` `error` code=1 PASS: tree built with 8 widgets (expect >= 8)
- `examples/ui/demo_progress_image_tooltip.spl` `error` code=1 PASS: tree built with 8 widgets
- `examples/ui/demo_table_list.spl` `error` code=1 PASS: tree built with widgets
- `examples/ui/demo_tabs_list_dialog.spl` `error` code=1 PASS: tree built with 18 widgets (expect >= 10)
- `examples/ui/demo_tree.spl` `error` code=1 PASS: tree built with 12 widgets (expect >= 5)
- `examples/ui/demo_validation.spl` `error` code=1 error: semantic: method `set_prop` not found on type `str` (receiver value: )
- `examples/ui/hello_async_electron.spl` `error` code=1 [2m2026-04-04T23:06:34.630820Z[0m [33m WARN[0m ThreadId(01) [1mrun_file_interpreted_with_args[0m[1m{[0m[3mpath[0m[2m=[0mexamples/ui/hello_async_electron.spl[1m}[0m[2m:[0m[1mevaluate_module[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["app", "ui", "electron", "async_app"][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["common", "ui", "session"][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["common", "ui", "capability_policy"][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["std", "security", "types"][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["std"][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m[][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["nogc_sync_mut", "platform"][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["nogc_sync_mut", "platform", "config"][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["nogc_sync_mut", "platform"][1m}[0m[2m:[0m [2msimple_compiler::interpreter::interpreter_module::module_loader[0m[2m:[0m [2m455:[0m Circular import detected, returning empty dict (no partial exports yet) [3mpath[0m[2m=[0m"/Users/ormastes/simple/src/lib/nogc_sync_mut/platform/__init__.spl"
- `examples/ui/hello_async_tauri.spl` `error` code=1 [2m2026-04-04T23:06:36.177857Z[0m [33m WARN[0m ThreadId(01) [1mrun_file_interpreted_with_args[0m[1m{[0m[3mpath[0m[2m=[0mexamples/ui/hello_async_tauri.spl[1m}[0m[2m:[0m[1mevaluate_module[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["app", "ui", "tauri", "async_app"][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["common", "ui", "session"][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["common", "ui", "capability_policy"][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["std", "security", "types"][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["std"][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m[][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["nogc_sync_mut", "platform"][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["nogc_sync_mut", "platform", "config"][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["nogc_sync_mut", "platform"][1m}[0m[2m:[0m [2msimple_compiler::interpreter::interpreter_module::module_loader[0m[2m:[0m [2m455:[0m Circular import detected, returning empty dict (no partial exports yet) [3mpath[0m[2m=[0m"/Users/ormastes/simple/src/lib/nogc_sync_mut/platform/__init__.spl"
- `examples/ui/hello_async_web.spl` `error` code=1 [2m2026-04-04T23:06:38.262422Z[0m [33m WARN[0m ThreadId(01) [1mrun_file_interpreted_with_args[0m[1m{[0m[3mpath[0m[2m=[0mexamples/ui/hello_async_web.spl[1m}[0m[2m:[0m[1mevaluate_module[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["app", "ui", "web", "async_server"][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["common", "ui", "session"][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["common", "ui", "capability_policy"][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["std", "security", "types"][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["std"][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m[][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["nogc_sync_mut", "platform"][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["nogc_sync_mut", "platform", "config"][1m}[0m[2m:[0m[1mload_and_merge_module[0m[1m{[0m[3mpath[0m[2m=[0m["nogc_sync_mut", "platform"][1m}[0m[2m:[0m [2msimple_compiler::interpreter::interpreter_module::module_loader[0m[2m:[0m [2m455:[0m Circular import detected, returning empty dict (no partial exports yet) [3mpath[0m[2m=[0m"/Users/ormastes/simple/src/lib/nogc_sync_mut/platform/__init__.spl"
- `examples/ui/hello_electron.spl` `error` code=1 error: example timed out after 10s: examples/ui/hello_electron.spl
- `examples/ui/hello_gui.spl` `error` code=1 error: semantic: unknown extern function: rt_term_get_size
- `examples/ui/hello_tauri.spl` `timeout` code=signal timed out
- `examples/ui/hello_web.spl` `timeout` code=signal timed out
- `examples/ui/launch_verified.spl` `error` code=1 error: semantic: unknown argument 'root_id'

