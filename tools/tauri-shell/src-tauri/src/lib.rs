// Simple Language UI — Tauri v2 Shell (library target)
//
// Shared app builder for desktop and mobile entry points.
// Desktop: main.rs calls run().
// Mobile:  tauri::mobile_entry_point calls run().

#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

use std::env;
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::thread;

use serde::Deserialize;
use tauri::{AppHandle, Manager, WebviewUrl, WebviewWindowBuilder};

include!(concat!(env!("OUT_DIR"), "/mobile_runtime_assets.rs"));

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

struct BundledRuntimeAsset {
    bytes: &'static [u8],
    filename: &'static str,
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
                if (typeof showDemoUI === 'function') {{ showDemoUI(); }}
                var root = document.getElementById('tauri-startup-error');
                if (!root) {{
                    root = document.createElement('div');
                    root.id = 'tauri-startup-error';
                    root.style.position = 'fixed';
                    root.style.top = '20px';
                    root.style.right = '20px';
                    root.style.width = 'min(520px, calc(100vw - 40px))';
                    root.style.maxHeight = 'calc(100vh - 40px)';
                    root.style.overflow = 'auto';
                    root.style.padding = '18px 20px';
                    root.style.borderRadius = '14px';
                    root.style.border = '1px solid rgba(255,180,171,0.42)';
                    root.style.background = 'rgba(33, 12, 18, 0.96)';
                    root.style.boxShadow = '0 18px 40px rgba(0,0,0,0.35)';
                    root.style.zIndex = '99999';
                    root.style.color = '#ffe2de';
                    root.style.fontFamily = '"SFMono-Regular","Consolas","Liberation Mono",monospace';
                    document.body.appendChild(root);
                }}
                root.innerHTML = '<div style="font-size:12px;letter-spacing:0.08em;text-transform:uppercase;color:#ffb4ab;margin-bottom:8px">Startup error</div>'
                    + '<div style="font-size:20px;font-weight:700;margin-bottom:10px;color:#fff0ee">' + `{}` + '</div>'
                    + '<pre style="white-space:pre-wrap;line-height:1.45;margin:0;color:#ffd7d2">' + `{}` + '</pre>';
                if (typeof window.simpleStatus === 'function') {{
                    window.simpleStatus(`{}`);
                }}
                console.warn(`{}` + ': ' + `{}`);
            }})();
            "#,
            escaped_title, escaped_detail, escaped_detail, escaped_title, escaped_detail
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
                    &format!(
                        "Subprocess produced non-IPC stdout:\n{}\n\nParse error: {}",
                        trimmed, e
                    ),
                );
            }
        }
    }
    eprintln!("[tauri-shell] subprocess stdout closed");
    update_status(
        &app,
        "Simple subprocess stdout closed before a valid render arrived.",
    );
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
            #[cfg(desktop)]
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
                    _ => {}
                }
            }
            #[cfg(not(desktop))]
            {
                let _ = action;
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
// Binary / entry resolution
// ---------------------------------------------------------------------------

fn resolve_external_url() -> Option<String> {
    let args: Vec<String> = env::args().collect();
    for i in 0..args.len() {
        if args[i] == "--url" && i + 1 < args.len() {
            return Some(args[i + 1].clone());
        }
    }
    env::var("SIMPLE_DASHBOARD_URL").ok()
}

fn resolve_simple_binary_from(
    args: &[String],
    env_bin: Option<String>,
    is_mobile: bool,
) -> Option<String> {
    if args.len() > 1 && !args[1].starts_with('-') {
        return Some(args[1].clone());
    }
    if let Some(bin) = env_bin {
        return Some(bin);
    }
    if is_mobile {
        None
    } else {
        Some("../../bin/simple".to_string())
    }
}

fn resolve_simple_binary() -> Option<String> {
    let args: Vec<String> = env::args().collect();
    let env_bin = env::var("SIMPLE_BIN").ok();
    resolve_simple_binary_from(&args, env_bin, cfg!(mobile))
}

#[cfg(mobile)]
fn bundled_mobile_runtime_asset() -> Option<BundledRuntimeAsset> {
    #[cfg(all(target_os = "android", target_arch = "aarch64"))]
    {
        return ANDROID_RUNTIME_AARCH64.map(|bytes| BundledRuntimeAsset {
            bytes,
            filename: "simple-aarch64-linux-android",
        });
    }
    #[cfg(all(target_os = "android", target_arch = "x86_64"))]
    {
        return ANDROID_RUNTIME_X86_64.map(|bytes| BundledRuntimeAsset {
            bytes,
            filename: "simple-x86_64-linux-android",
        });
    }
    #[cfg(all(target_os = "android", target_arch = "arm"))]
    {
        return ANDROID_RUNTIME_ARMV7.map(|bytes| BundledRuntimeAsset {
            bytes,
            filename: "simple-armv7-linux-androideabi",
        });
    }
    #[cfg(all(target_os = "android", target_arch = "x86"))]
    {
        return ANDROID_RUNTIME_I686.map(|bytes| BundledRuntimeAsset {
            bytes,
            filename: "simple-i686-linux-android",
        });
    }
    #[cfg(not(any(
        all(target_os = "android", target_arch = "aarch64"),
        all(target_os = "android", target_arch = "x86_64"),
        all(target_os = "android", target_arch = "arm"),
        all(target_os = "android", target_arch = "x86"),
    )))]
    None
}

#[cfg(not(mobile))]
fn bundled_mobile_runtime_asset() -> Option<BundledRuntimeAsset> {
    None
}

#[cfg(unix)]
fn mark_executable(path: &PathBuf) -> Result<(), String> {
    use std::os::unix::fs::PermissionsExt;

    let mut perms = fs::metadata(path)
        .map_err(|e| format!("failed to stat bundled runtime: {}", e))?
        .permissions();
    perms.set_mode(0o755);
    fs::set_permissions(path, perms).map_err(|e| format!("failed to chmod bundled runtime: {}", e))
}

#[cfg(not(unix))]
fn mark_executable(_path: &PathBuf) -> Result<(), String> {
    Ok(())
}

fn prepare_bundled_mobile_runtime() -> Result<Option<String>, String> {
    let Some(asset) = bundled_mobile_runtime_asset() else {
        return Ok(None);
    };

    let mut runtime_dir = env::temp_dir();
    runtime_dir.push("simple-tauri-shell");
    fs::create_dir_all(&runtime_dir)
        .map_err(|e| format!("failed to create mobile runtime dir: {}", e))?;

    let runtime_path = runtime_dir.join(asset.filename);
    let should_write = match fs::metadata(&runtime_path) {
        Ok(meta) => meta.len() != asset.bytes.len() as u64,
        Err(_) => true,
    };
    if should_write {
        fs::write(&runtime_path, asset.bytes)
            .map_err(|e| format!("failed to extract bundled mobile runtime: {}", e))?;
        mark_executable(&runtime_path)?;
    }

    Ok(Some(runtime_path.to_string_lossy().into_owned()))
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

fn shared_wm_requested() -> bool {
    if env::var("SIMPLE_UI_TAURI_SHARED_WM").as_deref() == Ok("1") {
        return true;
    }
    env::args().any(|arg| arg == "--shared-wm")
}

fn binary_supports_ui_command(simple_bin: &str) -> bool {
    let output = match Command::new(simple_bin).args(["ui", "--help"]).output() {
        Ok(out) => out,
        Err(err) => {
            eprintln!(
                "[tauri-shell] failed to probe '{} ui --help': {}",
                simple_bin, err
            );
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

// ---------------------------------------------------------------------------
// Shared entry point for desktop and mobile
// ---------------------------------------------------------------------------

#[cfg_attr(mobile, tauri::mobile_entry_point)]
pub fn run() {
    // Check for external URL mode (e.g. --url http://localhost:3000)
    let external_url = resolve_external_url();
    let shared_wm_requested = shared_wm_requested();
    let (simple_bin, mut startup_error): (Option<String>, Option<String>) =
        match resolve_simple_binary() {
            Some(path) => (Some(path), None),
            None => match prepare_bundled_mobile_runtime() {
                Ok(path) => (path, None),
                Err(err) => {
                    eprintln!(
                        "[tauri-shell] bundled mobile runtime extraction failed: {}",
                        err
                    );
                    (
                        None,
                        Some(format!(
                            "Bundled mobile runtime extraction failed.\n\n{}",
                            err
                        )),
                    )
                }
            },
        };
    let entry_file = resolve_entry_file();

    eprintln!("[tauri-shell] binary: {:?}", simple_bin);
    eprintln!("[tauri-shell] entry: {:?}", entry_file);
    eprintln!("[tauri-shell] external_url: {:?}", external_url);
    eprintln!("[tauri-shell] shared_wm_requested: {}", shared_wm_requested);
    log_entry_file_status(&entry_file);

    let mut child_stdout = None;
    let mut child_stderr = None;
    let mut child_stdin = None;
    let mut child_slot = None;

    // In URL mode, skip subprocess spawning entirely
    if shared_wm_requested {
        startup_error = Some(
            "WM-hosted mode is not wired through simple-tauri-shell yet.\n\nUse standalone Tauri mode without `--shared-wm`, or launch a backend with shared-WM support directly (for example the browser or electron host shells).".to_string()
        );
        eprintln!("[tauri-shell] refusing unsupported shared WM request");
    } else if external_url.is_none() {
        let ui_entry = entry_file
            .as_ref()
            .map(|entry| entry.ends_with(".ui.sdn"))
            .unwrap_or(false);

        if let Some(simple_bin) = simple_bin.as_ref() {
            if ui_entry && !binary_supports_ui_command(simple_bin) {
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
                let mut cmd = Command::new(simple_bin);
                if let Some(ref entry) = entry_file {
                    if entry.ends_with(".ui.sdn") {
                        cmd.arg("tauri-entry").arg(entry);
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
        } else {
            startup_error = Some(
                "Mobile shell started without a bundled Simple runtime.\n\nProvide an Android-compatible runtime at build time with one of:\n- SIMPLE_ANDROID_RUNTIME_AARCH64\n- SIMPLE_ANDROID_RUNTIME_X86_64\n- SIMPLE_ANDROID_RUNTIME_ARMV7\n- SIMPLE_ANDROID_RUNTIME_I686\n\nOr set `SIMPLE_BIN` to a valid mobile runtime path, or use `--url` / `SIMPLE_DASHBOARD_URL` to attach the shell to an external UI service.".to_string()
            );
            eprintln!("[tauri-shell] mobile mode has no bundled Simple binary; skipping subprocess launch");
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
        .manage(process_for_tauri.clone())
        .invoke_handler(tauri::generate_handler![
            send_keypress,
            send_action,
            send_resize,
        ])
        .setup(move |app| {
            let url = if let Some(ref ext_url) = external_url {
                eprintln!(
                    "[tauri-shell] creating window with external URL: {}",
                    ext_url
                );
                WebviewUrl::External(ext_url.parse().expect("invalid --url value"))
            } else {
                eprintln!("[tauri-shell] creating window from app://index.html");
                WebviewUrl::App("index.html".into())
            };

            let builder = WebviewWindowBuilder::new(app, "main", url);
            #[cfg(desktop)]
            let builder = builder.title("Simple UI").inner_size(1280.0, 720.0);
            let _win = builder.build()?;

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
                        update_status(
                            &handle,
                            "Waiting for first render from Simple subprocess...",
                        );
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
                                let collected =
                                    lines.lock().map(|l| l.join("\n")).unwrap_or_default();
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
        .on_window_event(move |_window, event| {
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
                // Window is already closing via the CloseRequested event.
                // No explicit close() needed (and it's not available on mobile).
            }
        })
        .run(tauri::generate_context!())
        .expect("tauri error");
}

#[cfg(test)]
mod tests {
    use super::resolve_simple_binary_from;
    use crate::{ANDROID_RUNTIME_AARCH64, ANDROID_RUNTIME_X86_64};

    #[test]
    fn desktop_defaults_to_repo_binary() {
        let args = vec!["simple-tauri-shell".to_string()];
        assert_eq!(
            resolve_simple_binary_from(&args, None, false),
            Some("../../bin/simple".to_string())
        );
    }

    #[test]
    fn mobile_requires_explicit_binary() {
        let args = vec!["simple-tauri-shell".to_string()];
        assert_eq!(resolve_simple_binary_from(&args, None, true), None);
    }

    #[test]
    fn explicit_binary_overrides_mobile_default() {
        let args = vec!["simple-tauri-shell".to_string()];
        assert_eq!(
            resolve_simple_binary_from(&args, Some("/data/local/tmp/simple".to_string()), true),
            Some("/data/local/tmp/simple".to_string())
        );
    }

    #[test]
    fn bundled_runtime_constants_are_absent_without_env() {
        assert!(ANDROID_RUNTIME_AARCH64.is_none() || !ANDROID_RUNTIME_AARCH64.unwrap().is_empty());
        assert!(ANDROID_RUNTIME_X86_64.is_none() || !ANDROID_RUNTIME_X86_64.unwrap().is_empty());
    }
}
