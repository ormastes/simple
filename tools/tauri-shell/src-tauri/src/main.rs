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
use tauri::{AppHandle, Emitter, Manager};

// ---------------------------------------------------------------------------
// IPC message types (subprocess → shell)
// ---------------------------------------------------------------------------

/// Incoming messages from the Simple subprocess.
///
/// The canonical protocol (protocol.spl) uses camelCase for the `type` tag
/// (e.g. `"windowControl"`), but the user-facing spec uses snake_case
/// (e.g. `"window_control"`).  We accept both via serde aliases.
#[derive(Debug, Deserialize)]
#[serde(tag = "type")]
enum SubprocessMessage {
    #[serde(rename = "render")]
    Render {
        html: String,
    },
    #[serde(rename = "dialog")]
    Dialog {
        #[serde(alias = "dialogType", alias = "dialog_type")]
        dialog_type: String,
        title: String,
        message: String,
    },
    #[serde(rename = "notification")]
    Notification {
        title: String,
        body: String,
    },
    /// Accepts both `"type":"windowControl"` and `"type":"window_control"`
    #[serde(rename = "windowControl", alias = "window_control")]
    WindowControl {
        action: String,
    },
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

// ---------------------------------------------------------------------------
// Subprocess stdout reader
// ---------------------------------------------------------------------------

fn read_subprocess_stdout(
    reader: BufReader<std::process::ChildStdout>,
    app: AppHandle,
) {
    for line in reader.lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => break,
        };

        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }

        match serde_json::from_str::<SubprocessMessage>(trimmed) {
            Ok(msg) => handle_subprocess_message(msg, &app),
            Err(e) => {
                eprintln!("[tauri-shell] failed to parse IPC: {} — line: {}", e, trimmed);
            }
        }
    }
    // Subprocess exited — close the window.
    if let Some(win) = app.get_webview_window("main") {
        let _ = win.close();
    }
}

fn handle_subprocess_message(msg: SubprocessMessage, app: &AppHandle) {
    match msg {
        SubprocessMessage::Render { html } => {
            let _ = app.emit("render", html);
        }
        SubprocessMessage::Dialog {
            dialog_type,
            title,
            message,
        } => {
            if let Some(win) = app.get_webview_window("main") {
                use tauri_plugin_dialog::DialogExt;
                match dialog_type.as_str() {
                    "confirm" => {
                        win.dialog()
                            .message(&message)
                            .title(&title)
                            .kind(tauri_plugin_dialog::MessageDialogKind::Info)
                            .blocking_show();
                    }
                    "alert" | _ => {
                        win.dialog()
                            .message(&message)
                            .title(&title)
                            .kind(tauri_plugin_dialog::MessageDialogKind::Info)
                            .blocking_show();
                    }
                }
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
                    "minimize" => {
                        let _ = win.minimize();
                    }
                    "maximize" => {
                        let _ = win.maximize();
                    }
                    "close" => {
                        let _ = win.close();
                    }
                    other => {
                        eprintln!("[tauri-shell] unknown window action: {}", other);
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Tauri commands (invoked from the webview JS)
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
    // 1. CLI arg: first argument after the program name
    let args: Vec<String> = env::args().collect();
    if args.len() > 1 && !args[1].starts_with('-') {
        return args[1].clone();
    }
    // 2. SIMPLE_BIN env var
    if let Ok(bin) = env::var("SIMPLE_BIN") {
        return bin;
    }
    // 3. Default relative path
    "../../bin/simple".to_string()
}

fn resolve_entry_file() -> Option<String> {
    let args: Vec<String> = env::args().collect();
    // The entry .spl file is the second positional arg (after the binary path)
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

    // Build subprocess command
    let mut cmd = Command::new(&simple_bin);
    if let Some(ref entry) = entry_file {
        cmd.arg("run").arg(entry);
    }
    cmd.stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit());

    let mut child = cmd.spawn().unwrap_or_else(|e| {
        eprintln!(
            "[tauri-shell] failed to spawn Simple binary at '{}': {}",
            simple_bin, e
        );
        std::process::exit(1);
    });

    let child_stdout = child.stdout.take().expect("failed to capture subprocess stdout");
    let child_stdin = child.stdin.take().expect("failed to capture subprocess stdin");

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
            let handle = app.handle().clone();

            // Spawn a thread to read from subprocess stdout
            let reader = BufReader::new(child_stdout);
            thread::spawn(move || {
                read_subprocess_stdout(reader, handle);
            });

            Ok(())
        })
        .on_window_event(move |window, event| {
            if let tauri::WindowEvent::CloseRequested { .. } = event {
                // Send quit message to subprocess
                process.send(&ShellMessage::Quit);

                // Give subprocess a moment then kill it
                let stdin_handle = Arc::clone(&process.stdin);
                if let Ok(mut guard) = stdin_handle.lock() {
                    // Drop stdin to signal EOF
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
        .expect("error while running tauri application");
}
