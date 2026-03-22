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

fn read_subprocess_stderr(reader: BufReader<std::process::ChildStderr>, app: AppHandle) {
    for line in reader.lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => break,
        };

        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }

        eprintln!("[tauri-shell] raw stderr: {}", trimmed);
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

fn main() {
    let simple_bin = resolve_simple_binary();
    let entry_file = resolve_entry_file();

    eprintln!("[tauri-shell] binary: {}", simple_bin);
    eprintln!("[tauri-shell] entry: {:?}", entry_file);

    // Spawn subprocess
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

    let mut child = cmd.spawn().unwrap_or_else(|e| {
        eprintln!("[tauri-shell] spawn failed '{}': {}", simple_bin, e);
        std::process::exit(1);
    });
    eprintln!("[tauri-shell] subprocess pid={}", child.id());

    let child_stdout = child.stdout.take().expect("no stdout");
    let child_stderr = child.stderr.take().expect("no stderr");
    let child_stdin = child.stdin.take().expect("no stdin");

    let process = Arc::new(SimpleProcess {
        stdin: Arc::new(Mutex::new(Some(child_stdin))),
        child: Mutex::new(Some(child)),
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

            // Start subprocess reader threads
            let handle = app.handle().clone();
            thread::spawn(move || {
                // Small delay to let the webview load the frontend shell first.
                thread::sleep(std::time::Duration::from_millis(500));
                update_status(&handle, "Waiting for first render from Simple subprocess...");
                read_subprocess_stdout(BufReader::new(child_stdout), handle);
            });
            let handle = app.handle().clone();
            thread::spawn(move || {
                thread::sleep(std::time::Duration::from_millis(500));
                read_subprocess_stderr(BufReader::new(child_stderr), handle);
            });

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
