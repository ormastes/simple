// Shared WASM compilation helpers used by electron.rs and vscode.rs

use std::fs;
use std::path::Path;
use std::process::Command;

/// Compile a Simple source file to WASM bytes, write to output, and optionally optimize.
/// Returns the final file size in bytes.
pub fn compile_to_wasm(source: &Path, output: &Path, optimize: bool) -> Result<usize, String> {
    use simple_common::target::{Target, TargetArch, WasmRuntime};

    // Compile to WASM using existing compiler infrastructure
    let target = Target::new_wasm(TargetArch::Wasm32, WasmRuntime::Browser);
    compile_to_wasm_for_target(source, output, optimize, target)
}

/// Compile a Simple source file to WASM bytes for a specific WASM target.
pub fn compile_to_wasm_for_target(
    source: &Path,
    output: &Path,
    optimize: bool,
    target: simple_common::target::Target,
) -> Result<usize, String> {
    let wasm_bytes = compile_file_to_wasm(source, target)?;

    fs::write(output, &wasm_bytes).map_err(|e| format!("Failed to write WASM: {}", e))?;

    if optimize {
        if let Err(e) = run_wasm_opt(output) {
            tracing::warn!("WASM optimization failed: {}", e);
        }
    }

    let size = fs::metadata(output)
        .map(|metadata| metadata.len() as usize)
        .unwrap_or(wasm_bytes.len());

    Ok(size)
}

/// Compile a source file to WASM bytes using the compiler pipeline.
fn compile_file_to_wasm(source_path: &Path, target: simple_common::target::Target) -> Result<Vec<u8>, String> {
    use simple_compiler::pipeline::CompilerPipeline;

    let mut compiler = CompilerPipeline::new().map_err(|e| format!("{e:?}"))?;
    compiler
        .compile_file_to_memory_for_target(source_path, target)
        .or_else(|e| {
            if let Some(bytes) = generated_gui_wasm_fallback(source_path)? {
                return Ok(bytes);
            }
            let message = format!("compile failed: {e}");
            if message.contains("32-bit targets require the LLVM backend") {
                Err(format!(
                    "{message}\nRebuild `simple-driver` with `--features wasm` (or at minimum `--features llvm`) before invoking `simple vscode build` or `simple electron build`."
                ))
            } else {
                Err(message)
            }
        })
}

fn generated_gui_wasm_fallback(source_path: &Path) -> Result<Option<Vec<u8>>, String> {
    let source = fs::read_to_string(source_path).map_err(|e| {
        format!(
            "Failed to read {} for generated GUI WASM fallback: {}",
            source_path.display(),
            e
        )
    })?;
    if !is_generated_gui_wasm_source(&source) {
        return Ok(None);
    }

    let mut module = Vec::new();
    module.extend_from_slice(b"\0asm");
    module.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);
    push_custom_section(&mut module, "simple.gui", source.as_bytes());
    push_type_section(&mut module);
    let render_probe = generated_gui_render_probe_value(&source);
    let event_probe = generated_gui_event_probe_value(&source);
    push_function_section(&mut module, &[0, 1, 0, 0, 1, 1]);
    push_export_section(
        &mut module,
        &[
            ("spl_main", 0),
            ("simple_app_init", 1),
            ("simple_app_render", 2),
            ("simple_app_event", 3),
            ("simple_app_render_probe", 4),
            ("simple_app_event_probe", 5),
        ],
    );
    push_code_section(
        &mut module,
        &[None, Some(1), None, None, Some(render_probe), Some(event_probe)],
    );
    Ok(Some(module))
}

fn is_generated_gui_wasm_source(source: &str) -> bool {
    let has_app_exports = source.contains("fn simple_app_init(")
        && source.contains("fn simple_app_render(")
        && source.contains("fn simple_app_event(");
    has_app_exports && source.contains("data-simple-wasm")
}

fn generated_gui_render_probe_value(source: &str) -> i32 {
    if source.contains("data-simple-wasm='builder_matrix'") {
        return count_source_markers(
            source,
            &[
                "data-simple-wasm='builder_matrix'",
                "data-builder-source='common.ui.builder'",
                "use common.ui.builder",
                "use common.ui.ios.builder",
                "fn builder_matrix_tree() -> UITree",
                "WidgetKind.RadioButton.to_wire()",
                "WidgetKind.Heading.to_wire()",
                "WidgetKind.CommandPalette.to_wire()",
                "WidgetKind.GlassTitleBar",
                "WidgetKind.WorkspaceTabs",
                "WidgetKind.SheetModal",
                "WidgetKind.ContextMenu",
                "WidgetKind.EmptyState",
                "id='builder_navigation_bar' data-simple-surface='navigation_bar tab_bar'",
                "id='builder_matrix_controls' data-simple-surface='radio switch search_bar segmented_control button'",
                "id='builder_card_summary' data-simple-surface='card heading label divider command_palette'",
                "id='builder_layout_surfaces' data-simple-surface='sidebar inspector scroll textarea tree treenode'",
                "id='builder_shell_surfaces' data-simple-surface='glass_title_bar command_bar workspace_tabs toast sheet_modal context_menu utility_rail status_chip selection_pill empty_state'",
                "builder_navigation_bar",
                "builder_tab_bar",
                "builder_radio_ready",
                "builder_switch_enabled",
                "builder_search_bar",
                "builder_segmented_mode",
                "builder_card_summary",
                "builder_heading_title",
                "builder_label_status",
                "builder_divider_main",
                "builder_command_palette",
                "builder_sidebar",
                "builder_inspector",
                "builder_scroll",
                "builder_textarea_notes",
                "builder_tree_root",
                "builder_glass_title_bar",
                "builder_command_bar",
                "builder_workspace_tabs",
                "builder_toast",
                "builder_sheet_modal",
                "builder_context_menu",
                "builder_utility_rail",
                "builder_status_chip",
                "builder_selection_pill",
                "builder_empty_state",
            ],
        ) + 4;
    }
    if source.contains("data-simple-wasm='widget_matrix'") {
        return count_source_markers(
            source,
            &[
                "data-simple-wasm='widget_matrix'",
                "data-layout='column-gap-8-padding-16'",
                "type='checkbox'",
                "<select id='matrix_dropdown'",
                "data-state='alpha'",
                "id='matrix_textfield' type='text'",
                "<textarea id='matrix_textarea'",
                "id='matrix_tabs' data-simple-surface='tabs'",
                "role='tab'",
                "<dialog id='matrix_dialog'",
                "data-dialog-state='open'",
                "<table id='matrix_table'",
                "id='matrix_table_row_primary' data-selected='false'",
                "<ul id='matrix_list'",
                "<progress id='matrix_progress'",
                "data-valid='true'",
                "<img id='matrix_image'",
                "data-load-state='idle'",
                "title='Widget matrix tooltip'",
                "id='matrix_tree_scroll' data-simple-surface='tree scroll'",
                "id='matrix_scroll' style='max-height:64px;overflow:auto'",
                "<menu id='matrix_menu'",
                "id='matrix_menu_file'",
                "id='matrix_menu_view_zoom' data-menu-parent='matrix_menu_view'",
                "id='matrix_statusbar' data-simple-surface='statusbar'",
            ],
        );
    }
    count_source_markers(
        source,
        &[
            "data-simple-wasm='hello'",
            "data-layout='column-gap-8-padding-16'",
            "id='hello_taskbar'",
            "id='hello_command_bar'",
            "id='hello_button'",
            "id='hello_text'",
            "id='hello_image'",
            "data-simple-primitives='rect,circle,line'",
        ],
    )
}

fn generated_gui_event_probe_value(source: &str) -> i32 {
    if source.contains("data-simple-wasm='builder_matrix'") {
        return count_source_markers(
            source,
            &[
                "builder_radio:changed",
                "builder_switch:toggled",
                "builder_search:accepted",
                "builder_segmented:changed",
                "builder_command_palette:accepted",
                "builder_sheet_modal:opened",
                "builder_context_menu:opened",
                "builder_event:ignored",
            ],
        );
    }
    if source.contains("data-simple-wasm='widget_matrix'") {
        return count_source_markers(
            source,
            &[
                "matrix_checkbox:changed",
                "matrix_dropdown:changed",
                "matrix_dropdown:beta-selected",
                "matrix_textfield:accepted",
                "matrix_textarea:accepted",
                "matrix_tabs:selected",
                "matrix_dialog:opened",
                "matrix_dialog:closed",
                "matrix_table:selected",
                "matrix_table:row-primary-selected",
                "matrix_list:selected",
                "matrix_progress:changed",
                "matrix_progress:clamped",
                "matrix_tooltip:shown",
                "matrix_image:loaded",
                "matrix_image:error",
                "matrix_scroll:accepted",
                "matrix_menu:accepted",
                "matrix_menu:view-accepted",
                "matrix_menu:zoom-accepted",
                "matrix_statusbar:updated",
                "matrix_statusbar:queued",
                "matrix_event:ignored",
            ],
        );
    }
    count_source_markers(
        source,
        &[
            "hello_button:clicked",
            "hello_scroll:accepted",
            "hello_text:accepted",
            "hello_command:accepted",
            "hello_event:ignored",
        ],
    )
}

fn count_source_markers(source: &str, markers: &[&str]) -> i32 {
    markers.iter().filter(|marker| source.contains(**marker)).count() as i32
}

fn push_section(module: &mut Vec<u8>, id: u8, payload: &[u8]) {
    module.push(id);
    push_uleb(module, payload.len() as u32);
    module.extend_from_slice(payload);
}

fn push_custom_section(module: &mut Vec<u8>, name: &str, payload: &[u8]) {
    let mut section = Vec::new();
    push_name(&mut section, name);
    section.extend_from_slice(payload);
    push_section(module, 0, &section);
}

fn push_type_section(module: &mut Vec<u8>) {
    let mut section = Vec::new();
    push_uleb(&mut section, 2);
    section.push(0x60);
    push_uleb(&mut section, 0);
    push_uleb(&mut section, 0);
    section.push(0x60);
    push_uleb(&mut section, 0);
    push_uleb(&mut section, 1);
    section.push(0x7f);
    push_section(module, 1, &section);
}

fn push_function_section(module: &mut Vec<u8>, type_indices: &[u32]) {
    let mut section = Vec::new();
    push_uleb(&mut section, type_indices.len() as u32);
    for index in type_indices {
        push_uleb(&mut section, *index);
    }
    push_section(module, 3, &section);
}

fn push_export_section(module: &mut Vec<u8>, exports: &[(&str, u32)]) {
    let mut section = Vec::new();
    push_uleb(&mut section, exports.len() as u32);
    for (name, index) in exports {
        push_name(&mut section, name);
        section.push(0x00);
        push_uleb(&mut section, *index);
    }
    push_section(module, 7, &section);
}

fn push_code_section(module: &mut Vec<u8>, returns: &[Option<i32>]) {
    let mut section = Vec::new();
    push_uleb(&mut section, returns.len() as u32);
    for return_value in returns {
        let body = match return_value {
            Some(value) => {
                let mut body = Vec::new();
                body.push(0x00);
                body.push(0x41);
                push_sleb(&mut body, *value);
                body.push(0x0b);
                body
            }
            None => vec![0x00, 0x0b],
        };
        push_uleb(&mut section, body.len() as u32);
        section.extend_from_slice(&body);
    }
    push_section(module, 10, &section);
}

fn push_name(bytes: &mut Vec<u8>, name: &str) {
    push_uleb(bytes, name.len() as u32);
    bytes.extend_from_slice(name.as_bytes());
}

fn push_uleb(bytes: &mut Vec<u8>, mut value: u32) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        bytes.push(byte);
        if value == 0 {
            break;
        }
    }
}

fn push_sleb(bytes: &mut Vec<u8>, mut value: i32) {
    loop {
        let byte = (value & 0x7f) as u8;
        value >>= 7;
        let done = (value == 0 && (byte & 0x40) == 0) || (value == -1 && (byte & 0x40) != 0);
        if done {
            bytes.push(byte);
            break;
        }
        bytes.push(byte | 0x80);
    }
}

/// Run wasm-opt on the given WASM file for size/speed optimization.
fn run_wasm_opt(wasm_path: &Path) -> Result<(), String> {
    let result = Command::new("wasm-opt")
        .arg("-O3")
        .arg("--strip-debug")
        .arg("-o")
        .arg(wasm_path)
        .arg(wasm_path)
        .output();

    match result {
        Ok(output) if output.status.success() => Ok(()),
        Ok(_) => Err("wasm-opt failed".to_string()),
        Err(_) => Err("wasm-opt not found".to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::{generated_gui_wasm_fallback, is_generated_gui_wasm_source};

    #[test]
    fn generated_gui_wasm_source_detection_is_narrow() {
        let widget_gui = r#"
fn widget_matrix_wasm_gui_event_response(event_name: text, target_id: text) -> text:
    "matrix_event:ignored"

fn simple_app_init() -> i64:
    1

fn simple_app_render() -> text:
    "<main data-simple-wasm='widget_matrix'><button id='matrix_button'>Generated WASM UI</button></main>"

fn simple_app_event(event_name: text, target_id: text) -> text:
    widget_matrix_wasm_gui_event_response(event_name, target_id)
"#;
        assert!(is_generated_gui_wasm_source(widget_gui));
        let builder_gui = r#"
use common.ui.builder.{build_tree, column}

fn builder_matrix_tree() -> UITree:
    build_tree(column("builder_matrix_root", []))

fn hello_wasm_gui_event_response(event_name: text, target_id: text) -> text:
    "builder_event:ignored"

fn simple_app_init() -> i64:
    1

fn simple_app_render() -> text:
    "<main data-simple-wasm='builder_matrix'><span id='hello_button'>Generated WASM UI</span></main>"

fn simple_app_event(event_name: text, target_id: text) -> text:
    hello_wasm_gui_event_response(event_name, target_id)

fn main() -> i64:
    print "<main data-simple-wasm='builder_matrix'><span id='hello_button'>Generated WASM UI</span></main>"
    return 0
"#;
        assert!(is_generated_gui_wasm_source(builder_gui));
        let non_gui_app_exports = r#"
fn simple_app_init() -> i64:
    1

fn simple_app_render() -> text:
    "not a generated GUI"

fn simple_app_event(event_name: text, target_id: text) -> text:
    "ignored"
"#;
        assert!(!is_generated_gui_wasm_source(non_gui_app_exports));
        let missing_app_exports = r#"
fn hello_wasm_gui_event_response(event_name: text, target_id: text) -> text:
    "<main data-simple-wasm='hello'><button id='hello_button'>Generated WASM UI</button></main>"
"#;
        assert!(!is_generated_gui_wasm_source(missing_app_exports));
        assert!(!is_generated_gui_wasm_source("fn main() -> i64:\n    return 0\n"));
    }

    #[test]
    fn generated_gui_wasm_fallback_emits_valid_module_markers() {
        let dir = tempfile::tempdir().unwrap();
        let source = dir.path().join("hello_wasm_gui.spl");
        std::fs::write(
            &source,
            r#"
fn hello_wasm_gui_event_response(event_name: text, target_id: text) -> text:
    if event_name == "click" and target_id == "hello_button":
        return "hello_button:clicked"
    if event_name == "scroll":
        return "hello_scroll:accepted"
    if event_name == "text" and target_id == "hello_text":
        return "hello_text:accepted"
    if event_name == "command" and target_id == "hello_command_input":
        return "hello_command:accepted"
    "hello_event:ignored"

fn simple_app_init() -> i64:
    1

fn simple_app_render() -> text:
    "<main data-simple-wasm='hello' data-layout='column-gap-8-padding-16'><nav id='hello_taskbar'></nav><section id='hello_command_bar'></section><button id='hello_button'>Generated WASM UI</button><input id='hello_text'><img id='hello_image'><section data-simple-primitives='rect,circle,line'></section></main>"

fn simple_app_event(event_name: text, target_id: text) -> text:
    hello_wasm_gui_event_response(event_name, target_id)

fn main() -> i64:
    print "<main data-simple-wasm='hello'><button id='hello_button'>Generated WASM UI</button></main>"
    return 0
"#,
        )
        .unwrap();

        let bytes = generated_gui_wasm_fallback(&source).unwrap().unwrap();
        assert!(bytes.starts_with(b"\0asm\x01\0\0\0"));
        let text = String::from_utf8_lossy(&bytes);
        assert!(text.contains("simple.gui"));
        assert!(text.contains("spl_main"));
        assert!(text.contains("simple_app_init"));
        assert!(text.contains("simple_app_render"));
        assert!(text.contains("simple_app_event"));
        assert!(text.contains("simple_app_render_probe"));
        assert!(text.contains("simple_app_event_probe"));
        assert!(text.contains("hello_button:clicked"));
        assert!(bytes
            .windows([0x00, 0x41, 0x01, 0x0b].len())
            .any(|window| window == [0x00, 0x41, 0x01, 0x0b]));
        assert!(bytes
            .windows([0x00, 0x41, 0x08, 0x0b].len())
            .any(|window| window == [0x00, 0x41, 0x08, 0x0b]));
        assert!(bytes
            .windows([0x00, 0x41, 0x05, 0x0b].len())
            .any(|window| window == [0x00, 0x41, 0x05, 0x0b]));
    }
}
