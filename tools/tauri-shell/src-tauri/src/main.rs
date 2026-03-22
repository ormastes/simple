// Simple Language UI — Tauri v2 Shell
//
// Spawns a Simple binary as a subprocess and communicates via JSON IPC
// over stdin/stdout.  The protocol is defined in src/app/ui.ipc/protocol.spl.

#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

use std::env;
use std::io::{BufRead, BufReader, Write};
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::thread;

use serde::Deserialize;
use tauri::{AppHandle, Manager, WebviewUrl, WebviewWindowBuilder};

// ---------------------------------------------------------------------------
// IPC message types (subprocess → shell)
// ---------------------------------------------------------------------------

#[derive(Debug, Deserialize)]
#[serde(tag = "type")]
enum SubprocessMessage {
    #[serde(rename = "render")]
    Render { html: String },
    #[serde(rename = "dialog")]
    Dialog {
        #[allow(dead_code)]
        #[serde(alias = "dialogType", alias = "dialog_type")]
        dialog_type: String,
        title: String,
        message: String,
    },
    #[serde(rename = "notification")]
    Notification { title: String, body: String },
    #[serde(rename = "windowControl", alias = "window_control")]
    WindowControl { action: String },
}

// ---------------------------------------------------------------------------
// IPC message types (shell → subprocess)
// ---------------------------------------------------------------------------

#[derive(Debug, serde::Serialize)]
#[serde(tag = "type", rename_all = "snake_case")]
enum ShellMessage {
    Keypress { key: String },
    Action { name: String },
    Resize { width: u32, height: u32 },
    Quit,
}

// ---------------------------------------------------------------------------
// Shared handle to the subprocess stdin
// ---------------------------------------------------------------------------

type StdinHandle = Arc<Mutex<Option<std::process::ChildStdin>>>;

struct SimpleProcess {
    stdin: StdinHandle,
    child: Mutex<Option<Child>>,
}

impl SimpleProcess {
    fn send(&self, msg: &ShellMessage) {
        if let Ok(mut guard) = self.stdin.lock() {
            if let Some(ref mut stdin) = *guard {
                if let Ok(json) = serde_json::to_string(msg) {
                    let _ = writeln!(stdin, "{}", json);
                    let _ = stdin.flush();
                }
            }
        }
    }
}

fn js_escape(text: &str) -> String {
    text.replace('\\', "\\\\")
        .replace('`', "\\`")
        .replace("${", "\\${")
}

fn show_error(app: &AppHandle, title: &str, detail: &str) {
    if let Some(win) = app.get_webview_window("main") {
        let escaped_title = js_escape(title);
        let escaped_detail = js_escape(detail);
        let js = format!(
            r#"
            (function() {{
                var app = document.getElementById('app');
                if (!app) {{
                    document.body.innerHTML = '<div id="app"></div>';
                    app = document.getElementById('app');
                }}
                app.innerHTML = '<div style="padding:24px;font-family:monospace">'
                    + '<h2 style="color:#e53e3e;margin-bottom:12px">' + `{}` + '</h2>'
                    + '<pre style="white-space:pre-wrap;background:#2d1b1b;color:#feb2b2;padding:16px;border-radius:8px;overflow:auto;max-height:80vh">'
                    + `{}` + '</pre></div>';
            }})();
            "#,
            escaped_title, escaped_detail
        );
        let _ = win.eval(&js);
    }
}

fn update_status(app: &AppHandle, message: &str) {
    if let Some(win) = app.get_webview_window("main") {
        let escaped = js_escape(message);
        let js = format!(
            r#"
            (function() {{
                if (typeof window.simpleStatus === 'function') {{
                    window.simpleStatus(`{}`);
                    return;
                }}
                var app = document.getElementById('app');
                if (app) {{
                    app.innerHTML = '<div style="padding:24px;font-family:monospace"><h2>Simple UI - Tauri</h2><pre style="white-space:pre-wrap;margin-top:12px">' + `{}` + '</pre></div>';
                }}
            }})();
            "#,
            escaped, escaped
        );
        let _ = win.eval(&js);
    }
}

// ---------------------------------------------------------------------------
// Subprocess stdout reader
// ---------------------------------------------------------------------------

fn read_subprocess_stdout(reader: BufReader<std::process::ChildStdout>, app: AppHandle) {
    for line in reader.lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => break,
        };

        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }

        eprintln!("[tauri-shell] raw stdout: {}", trimmed);

        match serde_json::from_str::<SubprocessMessage>(trimmed) {
            Ok(msg) => handle_subprocess_message(msg, &app),
            Err(e) => {
                eprintln!("[tauri-shell] parse error: {} — line: {}", e, trimmed);
                update_status(
                    &app,
                    &format!("Subprocess produced non-IPC stdout:\n{}\n\nParse error: {}", trimmed, e),
                );
            }
        }
    }
    eprintln!("[tauri-shell] subprocess stdout closed");
    update_status(&app, "Simple subprocess stdout closed before a valid render arrived.");
}

fn read_subprocess_stderr(
    reader: BufReader<std::process::ChildStderr>,
    app: AppHandle,
    stderr_lines: Arc<Mutex<Vec<String>>>,
) {
    for line in reader.lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => break,
        };

        let trimmed = line.trim().to_string();
        if trimmed.is_empty() {
            continue;
        }

        eprintln!("[tauri-shell] raw stderr: {}", trimmed);
        if let Ok(mut lines) = stderr_lines.lock() {
            lines.push(trimmed.clone());
        }
        update_status(&app, &format!("Simple subprocess stderr:\n{}", trimmed));
    }

    eprintln!("[tauri-shell] subprocess stderr closed");
}

fn handle_subprocess_message(msg: SubprocessMessage, app: &AppHandle) {
    match msg {
        SubprocessMessage::Render { html } => {
            eprintln!("[tauri-shell] render, html_len={}", html.len());
            if let Some(win) = app.get_webview_window("main") {
                let escaped = js_escape(&html);
                let js = format!(
                    r#"
                    (function() {{
                        var el = document.getElementById('app');
                        if (!el) {{
                            document.body.innerHTML = '<div id="app"></div>';
                            el = document.getElementById('app');
                        }}
                        el.innerHTML = `{}`;

                        if (!window._evtBound) {{
                            window._evtBound = true;
                            document.addEventListener('click', function(e) {{
                                var btn = e.target.closest('[data-action]');
                                if (btn && window.__TAURI_INTERNALS__) {{
                                    window.__TAURI_INTERNALS__.invoke('send_action', {{ name: btn.getAttribute('data-action') }});
                                }}
                            }});
                            document.addEventListener('keydown', function(e) {{
                                var key = e.key;
                                if (window.__TAURI_INTERNALS__ && (key.length === 1 || ['Enter','Escape','Backspace','Tab','ArrowUp','ArrowDown','ArrowLeft','ArrowRight'].indexOf(key) >= 0)) {{
                                    window.__TAURI_INTERNALS__.invoke('send_keypress', {{ key: key }});
                                }}
                            }});
                        }}
                    }})();
                    "#,
                    escaped
                );
                match win.eval(&js) {
                    Ok(_) => eprintln!("[tauri-shell] eval OK"),
                    Err(e) => eprintln!("[tauri-shell] eval FAIL: {}", e),
                }
            } else {
                eprintln!("[tauri-shell] window 'main' not found!");
            }
        }
        SubprocessMessage::Dialog {
            dialog_type: _,
            title,
            message,
        } => {
            if let Some(win) = app.get_webview_window("main") {
                use tauri_plugin_dialog::DialogExt;
                let _ = win
                    .dialog()
                    .message(&message)
                    .title(&title)
                    .kind(tauri_plugin_dialog::MessageDialogKind::Info)
                    .blocking_show();
            }
        }
        SubprocessMessage::Notification { title, body } => {
            use tauri_plugin_notification::NotificationExt;
            let _ = app
                .notification()
                .builder()
                .title(&title)
                .body(&body)
                .show();
        }
        SubprocessMessage::WindowControl { action } => {
            if let Some(win) = app.get_webview_window("main") {
                match action.as_str() {
                    "minimize" => { let _ = win.minimize(); }
                    "maximize" => { let _ = win.maximize(); }
                    "close" => { let _ = win.close(); }
                    _ => {}
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Tauri commands
// ---------------------------------------------------------------------------

#[tauri::command]
fn send_keypress(key: String, state: tauri::State<'_, Arc<SimpleProcess>>) {
    state.send(&ShellMessage::Keypress { key });
}

#[tauri::command]
fn send_action(name: String, state: tauri::State<'_, Arc<SimpleProcess>>) {
    state.send(&ShellMessage::Action { name });
}

#[tauri::command]
fn send_resize(width: u32, height: u32, state: tauri::State<'_, Arc<SimpleProcess>>) {
    state.send(&ShellMessage::Resize { width, height });
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

fn resolve_simple_binary() -> String {
    let args: Vec<String> = env::args().collect();
    if args.len() > 1 && !args[1].starts_with('-') {
        return args[1].clone();
    }
    if let Ok(bin) = env::var("SIMPLE_BIN") {
        return bin;
    }
    "../../bin/simple".to_string()
}

fn resolve_entry_file() -> Option<String> {
    let args: Vec<String> = env::args().collect();
    if args.len() > 2 && !args[2].starts_with('-') {
        Some(args[2].clone())
    } else if let Ok(entry) = env::var("SIMPLE_ENTRY") {
        Some(entry)
    } else {
        None
    }
}

fn binary_supports_ui_command(simple_bin: &str) -> bool {
    let output = match Command::new(simple_bin).args(["ui", "--help"]).output() {
        Ok(out) => out,
        Err(err) => {
            eprintln!("[tauri-shell] failed to probe '{} ui --help': {}", simple_bin, err);
            return false;
        }
    };

    let mut text = String::from_utf8_lossy(&output.stdout).to_string();
    if !output.stderr.is_empty() {
        text.push_str(&String::from_utf8_lossy(&output.stderr));
    }

    !text.contains("file not found: ui")
}

fn log_entry_file_status(entry_file: &Option<String>) {
    if let Some(entry) = entry_file {
        let path = std::path::Path::new(entry);
        let exists = path.exists();
        let readable = std::fs::File::open(path).is_ok();
        eprintln!(
            "[tauri-shell] entry file status: path='{}' exists={} readable={}",
            entry, exists, readable
        );
    } else {
        eprintln!("[tauri-shell] entry file status: no entry file provided");
    }
}

fn main() {
    let simple_bin = resolve_simple_binary();
    let entry_file = resolve_entry_file();

    eprintln!("[tauri-shell] binary: {}", simple_bin);
    eprintln!("[tauri-shell] entry: {:?}", entry_file);
    log_entry_file_status(&entry_file);

    let mut startup_error: Option<String> = None;
    let mut child_stdout = None;
    let mut child_stderr = None;
    let mut child_stdin = None;
    let mut child_slot = None;

    let ui_entry = entry_file
        .as_ref()
        .map(|entry| entry.ends_with(".ui.sdn"))
        .unwrap_or(false);

    if ui_entry && !binary_supports_ui_command(&simple_bin) {
        startup_error = Some(format!(
            "The selected Simple binary does not support `simple ui ...`.\n\nBinary: {}\nEntry: {}\n\nTauri HTML is loading correctly now, but this executable cannot launch the Simple UI subprocess for .ui.sdn files.",
            simple_bin,
            entry_file.clone().unwrap_or_default()
        ));
        eprintln!(
            "[tauri-shell] incompatible Simple binary for .ui.sdn launch: {}",
            simple_bin
        );
    } else {
        let mut cmd = Command::new(&simple_bin);
        if let Some(ref entry) = entry_file {
            if entry.ends_with(".ui.sdn") {
                cmd.arg("ui").arg("tauri").arg(entry);
            } else {
                cmd.arg("run").arg(entry);
            }
        }
        cmd.stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        match cmd.spawn() {
            Ok(mut child) => {
                eprintln!("[tauri-shell] subprocess pid={}", child.id());
                child_stdout = child.stdout.take();
                child_stderr = child.stderr.take();
                child_stdin = child.stdin.take();
                child_slot = Some(child);
            }
            Err(e) => {
                startup_error = Some(format!(
                    "Failed to spawn Simple subprocess.\n\nBinary: {}\nEntry: {:?}\nError: {}",
                    simple_bin, entry_file, e
                ));
                eprintln!("[tauri-shell] spawn failed '{}': {}", simple_bin, e);
            }
        }
    }

    let process = Arc::new(SimpleProcess {
        stdin: Arc::new(Mutex::new(child_stdin)),
        child: Mutex::new(child_slot),
    });

    let process_for_tauri = Arc::clone(&process);

    tauri::Builder::default()
        .plugin(tauri_plugin_dialog::init())
        .plugin(tauri_plugin_notification::init())
        .manage(process_for_tauri)
        .invoke_handler(tauri::generate_handler![
            send_keypress,
            send_action,
            send_resize,
        ])
        .setup(move |app| {
            eprintln!("[tauri-shell] creating window from app://index.html");

            let _win = WebviewWindowBuilder::new(
                app,
                "main",
                WebviewUrl::App("index.html".into()),
            )
            .title("Simple UI")
            .inner_size(1280.0, 720.0)
            .build()?;

            // Uncomment to debug: win.open_devtools();

            eprintln!("[tauri-shell] window created");

            let stderr_lines: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(Vec::new()));

            if let Some(message) = startup_error.clone() {
                let handle = app.handle().clone();
                thread::spawn(move || {
                    thread::sleep(std::time::Duration::from_millis(500));
                    show_error(&handle, "Startup Error", &message);
                });
            } else {
                if let Some(stdout) = child_stdout {
                    let handle = app.handle().clone();
                    thread::spawn(move || {
                        thread::sleep(std::time::Duration::from_millis(500));
                        update_status(&handle, "Waiting for first render from Simple subprocess...");
                        read_subprocess_stdout(BufReader::new(stdout), handle);
                    });
                }
                if let Some(stderr) = child_stderr {
                    let handle = app.handle().clone();
                    let lines = Arc::clone(&stderr_lines);
                    thread::spawn(move || {
                        thread::sleep(std::time::Duration::from_millis(500));
                        read_subprocess_stderr(BufReader::new(stderr), handle, lines);
                    });
                }
                // Monitor subprocess exit code
                {
                    let handle = app.handle().clone();
                    let proc = Arc::clone(&process_for_tauri);
                    let lines = Arc::clone(&stderr_lines);
                    thread::spawn(move || {
                        let exit_status = {
                            let mut guard = match proc.child.lock() {
                                Ok(g) => g,
                                Err(_) => return,
                            };
                            match guard.as_mut() {
                                Some(child) => child.wait().ok(),
                                None => return,
                            }
                        };
                        if let Some(status) = exit_status {
                            if !status.success() {
                                let code = status.code().unwrap_or(-1);
                                let collected = lines.lock().map(|l| l.join("\n")).unwrap_or_default();
                                let msg = if collected.is_empty() {
                                    format!("Simple subprocess exited with code {}.", code)
                                } else {
                                    format!(
                                        "Simple subprocess exited with code {}.\n\nStderr:\n{}",
                                        code, collected
                                    )
                                };
                                eprintln!("[tauri-shell] subprocess exited with code {}", code);
                                show_error(&handle, "Subprocess Failed", &msg);
                            } else {
                                eprintln!("[tauri-shell] subprocess exited successfully");
                            }
                        }
                    });
                }
            }

            Ok(())
        })
        .on_window_event(move |window, event| {
            if let tauri::WindowEvent::CloseRequested { .. } = event {
                process.send(&ShellMessage::Quit);
                if let Ok(mut guard) = process.stdin.lock() {
                    *guard = None;
                }
                if let Ok(mut guard) = process.child.lock() {
                    if let Some(ref mut child) = *guard {
                        let _ = child.kill();
                        let _ = child.wait();
                    }
                }
                let _ = window.close();
            }
        })
        .run(tauri::generate_context!())
        .expect("tauri error");
}
