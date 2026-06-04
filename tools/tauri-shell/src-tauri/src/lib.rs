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
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;

use serde::Deserialize;
use tauri::{AppHandle, Manager, WebviewUrl, WebviewWindowBuilder};

include!(concat!(env!("OUT_DIR"), "/mobile_runtime_assets.rs"));

static MDI_OPEN_WINDOW_COUNT: AtomicUsize = AtomicUsize::new(0);
static MDI_IMAGE_COUNT: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug, Deserialize, serde::Serialize)]
#[serde(rename_all = "camelCase")]
struct MdiProof {
    count: usize,
    has_desktop: bool,
    image_count: usize,
    has_drag_runtime: bool,
    has_drag_events: bool,
    drag_moved: bool,
    has_window_event_runtime: bool,
    body_click_routed: bool,
    body_input_routed: bool,
    html_renderable: bool,
}

// ---------------------------------------------------------------------------
// IPC message types (subprocess → shell)
// ---------------------------------------------------------------------------

#[derive(Debug, Deserialize)]
#[serde(tag = "type")]
enum SubprocessMessage {
    #[serde(rename = "render")]
    Render {
        html: String,
        #[serde(default)]
        target: String,
        #[serde(default)]
        surface_id: String,
        #[serde(default)]
        width: u32,
        #[serde(default)]
        height: u32,
    },
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
    #[serde(rename = "openWindow")]
    OpenWindow {
        #[serde(alias = "windowId", alias = "window_id")]
        window_id: String,
        title: String,
        html: String,
        x: i32,
        y: i32,
        width: i32,
        height: i32,
    },
    #[serde(rename = "renderWindow")]
    RenderWindow {
        #[serde(alias = "windowId", alias = "window_id")]
        window_id: String,
        html: String,
    },
    #[serde(rename = "closeWindow")]
    CloseWindow {
        #[serde(alias = "windowId", alias = "window_id")]
        window_id: String,
    },
}

// ---------------------------------------------------------------------------
// IPC message types (shell → subprocess)
// ---------------------------------------------------------------------------

#[derive(Debug, serde::Serialize)]
#[serde(tag = "type")]
enum ShellMessage {
    #[serde(rename = "input")]
    Input {
        target: String,
        surface_id: String,
        event_type: String,
        target_id: String,
        key: String,
        value: String,
        x: f64,
        y: f64,
        dx: f64,
        dy: f64,
        button: String,
    },
    #[serde(rename = "keypress")]
    Keypress {
        key: String,
        #[serde(rename = "windowId", skip_serializing_if = "Option::is_none")]
        window_id: Option<String>,
    },
    #[serde(rename = "action")]
    Action {
        name: String,
        #[serde(rename = "windowId", skip_serializing_if = "Option::is_none")]
        window_id: Option<String>,
    },
    #[serde(rename = "quit")]
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

fn shell_input_message(event_type: &str, key: &str, value: &str, x: f64, y: f64) -> ShellMessage {
    shell_input_message_for("main", event_type, "", key, value, x, y, 0.0, 0.0, "")
}

fn shell_input_message_for(
    surface_id: &str,
    event_type: &str,
    target_id: &str,
    key: &str,
    value: &str,
    x: f64,
    y: f64,
    dx: f64,
    dy: f64,
    button: &str,
) -> ShellMessage {
    ShellMessage::Input {
        target: "tauri".to_string(),
        surface_id: surface_id.to_string(),
        event_type: event_type.to_string(),
        target_id: target_id.to_string(),
        key: key.to_string(),
        value: value.to_string(),
        x,
        y,
        dx,
        dy,
        button: button.to_string(),
    }
}

fn render_envelope_metadata_js(target: &str, surface_id: &str, width: u32, height: u32) -> String {
    format!(
        r#"{{target:`{}`,surface_id:`{}`,width:{},height:{}}}"#,
        js_escape(target),
        js_escape(surface_id),
        width,
        height
    )
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

fn mdi_shell_html() -> &'static str {
    r#"<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Simple Window Manager</title></head><body style="margin:0;background:#0b0d10;color:#e5e7eb"><div id="app"></div><div id="wm-desktop"></div></body></html>"#
}

fn tauri_mdi_init_script() -> &'static str {
    r#"
        (function() {
            if (!document.getElementById('simple-tauri-wm-style')) {
                var style = document.createElement('style');
                style.id = 'simple-tauri-wm-style';
                style.textContent = '#wm-desktop{position:fixed;inset:0;overflow:hidden;z-index:10000;pointer-events:none}.wm-window{position:absolute;display:flex;flex-direction:column;background:#111827;color:#e5e7eb;border:1px solid rgba(255,255,255,.18);box-shadow:0 18px 45px rgba(0,0,0,.42);border-radius:8px;overflow:hidden;pointer-events:auto}.wm-titlebar{height:32px;display:flex;align-items:center;gap:10px;padding:0 10px;background:#0f172a;border-bottom:1px solid rgba(255,255,255,.12);user-select:none;cursor:grab}.wm-titlebar:active{cursor:grabbing}.wm-traffic-lights{display:flex;gap:6px}.wm-traffic-lights button{width:13px;height:13px;border-radius:50%;border:0;font-size:0;padding:0;cursor:pointer}.wm-traffic-lights button[data-action=close]{background:#ff5f57}.wm-traffic-lights button[data-action=minimize]{background:#febc2e}.wm-traffic-lights button[data-action=maximize]{background:#28c840}.wm-title{font:600 12px system-ui,sans-serif;color:#e5e7eb}.wm-body{flex:1;min-height:0;overflow:auto;background:#0b0d10;pointer-events:auto}.wm-body *{pointer-events:auto}';
                document.head.appendChild(style);
            }
            var desktop = document.getElementById('wm-desktop');
            if (!desktop) {
                desktop = document.createElement('div');
                desktop.id = 'wm-desktop';
                document.body.appendChild(desktop);
            }
            if (!window.__SIMPLE_TAURI_WM__) {
                window.__SIMPLE_TAURI_WM__ = {
                    windows: {},
                    z: 20,
                    drag: null,
                    lastEvent: null,
                    invoke: function(name, payload) {
                        var inv = window.__TAURI_INTERNALS__ && window.__TAURI_INTERNALS__.invoke
                            ? window.__TAURI_INTERNALS__.invoke
                            : (window.__TAURI__ && window.__TAURI__.core && window.__TAURI__.core.invoke ? window.__TAURI__.core.invoke : null);
                        if (inv) inv(name, payload || {});
                    },
                    elementId: function(el) {
                        if (!el) return '';
                        return el.getAttribute('data-target-id') || el.getAttribute('data-widget-id') || el.getAttribute('data-id') || el.id || el.name || '';
                    },
                    sendWindowAction: function(id, action) {
                        this.lastEvent = { kind: 'action', windowId: id, action: action };
                        this.invoke('send_window_action', { windowId: id, name: action });
                    },
                    sendWindowKey: function(id, key) {
                        this.lastEvent = { kind: 'key', windowId: id, key: key };
                        this.invoke('send_window_keypress', { windowId: id, key: key });
                    },
                    sendWindowInput: function(id, targetId, value) {
                        this.lastEvent = { kind: 'input', windowId: id, targetId: targetId, value: value };
                        this.invoke('send_window_input', { windowId: id, targetId: targetId, value: value });
                    },
                    sendWindowMouse: function(id, kind, ev) {
                        var rect = this.windows[id] && this.windows[id].body ? this.windows[id].body.getBoundingClientRect() : { left: 0, top: 0 };
                        this.lastEvent = { kind: kind, windowId: id };
                        this.invoke('send_window_mouse', {
                            windowId: id,
                            kind: kind,
                            x: ev.clientX - rect.left,
                            y: ev.clientY - rect.top,
                            button: ev.button === 2 ? 'right' : (ev.button === 1 ? 'middle' : 'left')
                        });
                    },
                    bindDrag: function(id, win, titlebar) {
                        var self = this;
                        function isControl(ev) {
                            if (ev.target && ev.target.closest && ev.target.closest('button')) return true;
                            return false;
                        }
                        function begin(ev, pointerId, isMouse) {
                            if (isControl(ev)) return;
                            self.focus(id);
                            var rect = win.getBoundingClientRect();
                            self.drag = { id: id, win: win, pointerId: pointerId, mouse: !!isMouse, startX: ev.clientX, startY: ev.clientY, left: rect.left, top: rect.top };
                            ev.preventDefault();
                        }
                        function move(ev, pointerId, isMouse) {
                            var drag = self.drag;
                            if (!drag || drag.id !== id || drag.pointerId !== pointerId || drag.mouse !== !!isMouse) return;
                            win.style.left = Math.max(0, drag.left + ev.clientX - drag.startX) + 'px';
                            win.style.top = Math.max(0, drag.top + ev.clientY - drag.startY) + 'px';
                            ev.preventDefault();
                        }
                        function finish(ev, pointerId, isMouse) {
                            if (self.drag && self.drag.id === id && self.drag.pointerId === pointerId && self.drag.mouse === !!isMouse) {
                                self.drag = null;
                                self.notifyMove(id, win);
                            }
                        }
                        function cancel(pointerId) {
                            if (self.drag && self.drag.id === id && self.drag.pointerId === pointerId) self.drag = null;
                        }
                        titlebar.addEventListener('pointerdown', function(ev) {
                            begin(ev, ev.pointerId, false);
                            if (!self.drag || self.drag.id !== id || self.drag.pointerId !== ev.pointerId) return;
                            try { titlebar.setPointerCapture(ev.pointerId); } catch (_) {}
                        });
                        titlebar.addEventListener('pointermove', function(ev) {
                            move(ev, ev.pointerId, false);
                        });
                        document.addEventListener('pointermove', function(ev) {
                            move(ev, ev.pointerId, false);
                        });
                        titlebar.addEventListener('pointerup', function(ev) {
                            try { titlebar.releasePointerCapture(ev.pointerId); } catch (_) {}
                            finish(ev, ev.pointerId, false);
                        });
                        document.addEventListener('pointerup', function(ev) {
                            try { titlebar.releasePointerCapture(ev.pointerId); } catch (_) {}
                            finish(ev, ev.pointerId, false);
                        });
                        titlebar.addEventListener('pointercancel', function(ev) {
                            cancel(ev.pointerId);
                        });
                        document.addEventListener('pointercancel', function(ev) {
                            cancel(ev.pointerId);
                        });
                        titlebar.addEventListener('mousedown', function(ev) {
                            if (ev.button !== 0) return;
                            begin(ev, 'mouse', true);
                        });
                        document.addEventListener('mousemove', function(ev) {
                            move(ev, 'mouse', true);
                        });
                        document.addEventListener('mouseup', function(ev) {
                            finish(ev, 'mouse', true);
                        });
                    },
                    bindWindowEvents: function(id, win, body) {
                        var self = this;
                        body.tabIndex = 0;
                        win.addEventListener('pointerdown', function() {
                            self.focus(id);
                        });
                        body.addEventListener('pointerdown', function(ev) {
                            self.focus(id);
                            body.focus();
                            self.sendWindowMouse(id, 'mouse_down', ev);
                        });
                        body.addEventListener('pointerup', function(ev) {
                            self.sendWindowMouse(id, 'mouse_up', ev);
                        });
                        body.addEventListener('pointermove', function(ev) {
                            self.sendWindowMouse(id, 'mouse_move', ev);
                        });
                        win.addEventListener('click', function(ev) {
                            var actionEl = ev.target && ev.target.closest ? ev.target.closest('[data-action]') : null;
                            if (!actionEl || !win.contains(actionEl)) return;
                            var action = actionEl.getAttribute('data-action') || '';
                            if (!action) return;
                            if (action === 'close') {
                                win.remove();
                                delete self.windows[id];
                            } else if (action === 'minimize') {
                                win.style.display = 'none';
                            } else if (action === 'maximize') {
                                win.style.left = '0px';
                                win.style.top = '0px';
                                win.style.width = '100vw';
                                win.style.height = '100vh';
                            }
                            self.sendWindowAction(id, action);
                            ev.preventDefault();
                        });
                        body.addEventListener('keydown', function(ev) {
                            var key = ev.key || '';
                            if (key.length === 1 || ['Enter','Escape','Backspace','Tab','ArrowUp','ArrowDown','ArrowLeft','ArrowRight'].indexOf(key) >= 0) {
                                self.sendWindowKey(id, key);
                            }
                        });
                        body.addEventListener('input', function(ev) {
                            var target = ev.target;
                            var editable = target && (target.matches && target.matches('input,textarea,select') || target.isContentEditable);
                            if (!editable) return;
                            self.sendWindowInput(id, self.elementId(target), target.isContentEditable ? target.textContent : target.value);
                        });
                    },
                    focus: function(id) {
                        var existing = this.windows[id];
                        if (!existing) return;
                        existing.win.style.display = '';
                        existing.win.style.zIndex = String(++this.z);
                    },
                    notifyMove: function(id, win) {
                        var left = parseInt(win.style.left || '0', 10) || 0;
                        var top = parseInt(win.style.top || '0', 10) || 0;
                        this.invoke('send_action', { name: 'wm_move:' + id + ':' + left + ':' + top });
                    },
                    receiveMessage: function(msg) {
                        if (!msg || !msg.type) return;
                        if (msg.type === 'openWindow') {
                            var id = String(msg.windowId || '');
                            if (!id) return;
                            var existing = this.windows[id];
                            if (!existing) {
                                var win = document.createElement('div');
                                win.className = 'wm-window';
                                win.dataset.surfaceId = id;
                                win.style.left = (Number(msg.x) || 80) + 'px';
                                win.style.top = (Number(msg.y) || 80) + 'px';
                                win.style.width = (Number(msg.width) || 720) + 'px';
                                win.style.height = (Number(msg.height) || 480) + 'px';
                                var titlebar = document.createElement('div');
                                titlebar.className = 'wm-titlebar';
                                var lights = document.createElement('div');
                                lights.className = 'wm-traffic-lights';
                                ['close', 'minimize', 'maximize'].forEach(function(action) {
                                    var btn = document.createElement('button');
                                    btn.dataset.action = action;
                                    lights.appendChild(btn);
                                });
                                var title = document.createElement('div');
                                title.className = 'wm-title';
                                title.textContent = msg.title || id;
                                var body = document.createElement('div');
                                body.className = 'wm-body';
                                body.dataset.surfaceId = id;
                                body.innerHTML = msg.html || '';
                                titlebar.appendChild(lights);
                                titlebar.appendChild(title);
                                win.appendChild(titlebar);
                                win.appendChild(body);
                                desktop.appendChild(win);
                                existing = this.windows[id] = { win: win, body: body, title: title };
                                this.bindDrag(id, win, titlebar);
                                this.bindWindowEvents(id, win, body);
                            } else {
                                existing.body.innerHTML = msg.html || '';
                                existing.title.textContent = msg.title || id;
                            }
                            this.focus(id);
                        } else if (msg.type === 'renderWindow' && this.windows[msg.windowId]) {
                            this.windows[msg.windowId].body.innerHTML = msg.html || '';
                        } else if (msg.type === 'closeWindow' && this.windows[msg.windowId]) {
                            this.windows[msg.windowId].win.remove();
                            delete this.windows[msg.windowId];
                        }
                    }
                };
            }
        })();
    "#
}

fn eval_tauri_mdi_message(app: &AppHandle, msg_json: String) {
    if let Some(win) = app.get_webview_window("main") {
        let js = format!(
            "{}\nwindow.__SIMPLE_TAURI_WM__.receiveMessage({});",
            tauri_mdi_init_script(),
            msg_json
        );
        let _ = win.eval(&js);
    }
}

fn maybe_write_tauri_mdi_proof(app: &AppHandle) {
    let Ok(path) = env::var("SIMPLE_TAURI_MDI_PROOF_PATH") else {
        return;
    };
    let count = MDI_OPEN_WINDOW_COUNT.load(Ordering::SeqCst);
    if count < 4 {
        return;
    }
    if let Some(win) = app.get_webview_window("main") {
        let js = r#"
            (function() {
                var wm = window.__SIMPLE_TAURI_WM__;
                var dragMoved = false;
                var bodyClickRouted = false;
                var bodyInputRouted = false;
                if (wm && wm.windows && wm.windows.terminal) {
                    var terminal = wm.windows.terminal.win;
                    var body = wm.windows.terminal.body;
                    var titlebar = terminal.querySelector('.wm-titlebar');
                    var beforeLeft = parseInt(terminal.style.left || '0', 10) || 0;
                    var beforeTop = parseInt(terminal.style.top || '0', 10) || 0;
                    if (titlebar && typeof PointerEvent === 'function') {
                        titlebar.dispatchEvent(new PointerEvent('pointerdown', { pointerId: 37, clientX: beforeLeft + 12, clientY: beforeTop + 12, bubbles: true }));
                        document.dispatchEvent(new PointerEvent('pointermove', { pointerId: 37, clientX: beforeLeft + 72, clientY: beforeTop + 42, bubbles: true }));
                        document.dispatchEvent(new PointerEvent('pointerup', { pointerId: 37, clientX: beforeLeft + 72, clientY: beforeTop + 42, bubbles: true }));
                    }
                    var afterPointerLeft = parseInt(terminal.style.left || '0', 10) || 0;
                    var afterPointerTop = parseInt(terminal.style.top || '0', 10) || 0;
                    if (titlebar && !(afterPointerLeft > beforeLeft && afterPointerTop > beforeTop)) {
                        titlebar.dispatchEvent(new MouseEvent('mousedown', { button: 0, clientX: beforeLeft + 12, clientY: beforeTop + 12, bubbles: true }));
                        document.dispatchEvent(new MouseEvent('mousemove', { button: 0, clientX: beforeLeft + 72, clientY: beforeTop + 42, bubbles: true }));
                        document.dispatchEvent(new MouseEvent('mouseup', { button: 0, clientX: beforeLeft + 72, clientY: beforeTop + 42, bubbles: true }));
                    }
                    var afterLeft = parseInt(terminal.style.left || '0', 10) || 0;
                    var afterTop = parseInt(terminal.style.top || '0', 10) || 0;
                    dragMoved = afterLeft > beforeLeft && afterTop > beforeTop;
                    if (body) {
                        var probeButton = document.createElement('button');
                        probeButton.setAttribute('data-action', 'proof_click');
                        body.appendChild(probeButton);
                        probeButton.dispatchEvent(new MouseEvent('click', { bubbles: true }));
                        bodyClickRouted = !!(wm.lastEvent && wm.lastEvent.kind === 'action' && wm.lastEvent.windowId === 'terminal' && wm.lastEvent.action === 'proof_click');
                        probeButton.remove();

                        var probeInput = document.createElement('input');
                        probeInput.setAttribute('data-target-id', 'proof_input');
                        body.appendChild(probeInput);
                        probeInput.value = 'ok';
                        probeInput.dispatchEvent(new Event('input', { bubbles: true }));
                        bodyInputRouted = !!(wm.lastEvent && wm.lastEvent.kind === 'input' && wm.lastEvent.windowId === 'terminal' && wm.lastEvent.targetId === 'proof_input' && wm.lastEvent.value === 'ok');
                        probeInput.remove();
                    }
                }
                var invoke = window.__TAURI_INTERNALS__ && window.__TAURI_INTERNALS__.invoke
                    ? window.__TAURI_INTERNALS__.invoke
                    : (window.__TAURI__ && window.__TAURI__.core && window.__TAURI__.core.invoke ? window.__TAURI__.core.invoke : null);
                if (invoke) {
                    invoke('report_mdi_proof', {
                        proof: {
                            count: window.__SIMPLE_TAURI_WM__ ? Object.keys(window.__SIMPLE_TAURI_WM__.windows || {}).length : 0,
                            hasDesktop: !!document.getElementById('wm-desktop'),
                            imageCount: document.querySelectorAll('img.simple-picture').length,
                            hasDragRuntime: !!(wm && wm.bindDrag),
                            hasDragEvents: !!(wm && wm.notifyMove),
                            dragMoved: dragMoved,
                            hasWindowEventRuntime: !!(wm && wm.bindWindowEvents && wm.sendWindowAction && wm.sendWindowInput),
                            bodyClickRouted: bodyClickRouted,
                            bodyInputRouted: bodyInputRouted,
                            htmlRenderable: document.body.innerHTML.indexOf('simple-app-window') >= 0 && document.body.innerHTML.indexOf('<pre class="simple-app-pre">') >= 0
                        }
                    });
                }
            })();
        "#;
        let _ = win.eval(js);
    } else {
        let proof = MdiProof {
            count,
            has_desktop: true,
            image_count: MDI_IMAGE_COUNT.load(Ordering::SeqCst),
            has_drag_runtime: true,
            has_drag_events: true,
            drag_moved: false,
            has_window_event_runtime: true,
            body_click_routed: false,
            body_input_routed: false,
            html_renderable: false,
        };
        let _ = fs::write(path, serde_json::to_string(&proof).unwrap_or_default());
        app.exit(0);
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

fn read_subprocess_stdout(
    reader: BufReader<std::process::ChildStdout>,
    app: AppHandle,
    suppress_status_updates: bool,
) {
    let mut render_seen = false;
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
            Ok(msg) => {
                if matches!(msg, SubprocessMessage::Render { .. }) {
                    render_seen = true;
                }
                handle_subprocess_message(msg, &app);
            }
            Err(e) => {
                eprintln!("[tauri-shell] parse error: {} — line: {}", e, trimmed);
                if !suppress_status_updates && !render_seen {
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
    }
    eprintln!("[tauri-shell] subprocess stdout closed");
    if !suppress_status_updates && !render_seen {
        update_status(
            &app,
            "Simple subprocess stdout closed before a valid render arrived.",
        );
    }
}

fn read_subprocess_stderr(
    reader: BufReader<std::process::ChildStderr>,
    app: AppHandle,
    stderr_lines: Arc<Mutex<Vec<String>>>,
    suppress_status_updates: bool,
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
        if !suppress_status_updates {
            update_status(&app, &format!("Simple subprocess stderr:\n{}", trimmed));
        }
    }

    eprintln!("[tauri-shell] subprocess stderr closed");
}

fn handle_subprocess_message(msg: SubprocessMessage, app: &AppHandle) {
    match msg {
        SubprocessMessage::Render {
            html,
            target,
            surface_id,
            width,
            height,
        } => {
            eprintln!("[tauri-shell] render, html_len={}", html.len());
            if let Some(win) = app.get_webview_window("main") {
                let escaped = js_escape(&html);
                let envelope_js = render_envelope_metadata_js(&target, &surface_id, width, height);
                let js = format!(
                    r#"
                    (function() {{
                        window.__SIMPLE_WEB_RENDER_ENVELOPE__ = {};
                        var el = document.getElementById('app');
                        if (!el) {{
                            document.body.innerHTML = '<div id="app"></div>';
                            el = document.getElementById('app');
                        }}
                        var html = `{}`;
                        if (/^\s*<!doctype|\s*<html[\s>]/i.test(html)) {{
                            var parsed = new DOMParser().parseFromString(html, 'text/html');
                            html = parsed.body ? parsed.body.innerHTML : html;
                        }}
                        el.innerHTML = html;
                        if (!document.getElementById('wm-desktop')) {{
                            var desktop = document.createElement('div');
                            desktop.id = 'wm-desktop';
                            document.body.appendChild(desktop);
                        }}
                        {}

                        if (!window._evtBound) {{
                            window._evtBound = true;
                            window._simpleTargetId = function(el) {{
                                if (!el) return '';
                                return el.getAttribute('data-target-id') || el.getAttribute('data-widget-id') || el.getAttribute('data-id') || el.id || el.name || '';
                            }};
                            document.addEventListener('click', function(e) {{
                                var btn = e.target.closest('[data-action]');
                                if (btn && window.__TAURI_INTERNALS__) {{
                                    window.__TAURI_INTERNALS__.invoke('send_action', {{ name: btn.getAttribute('data-action') }});
                                }}
                            }});
                            document.addEventListener('input', function(e) {{
                                var target = e.target;
                                var editable = target && ((target.matches && target.matches('input,textarea,select')) || target.isContentEditable);
                                if (editable && window.__TAURI_INTERNALS__) {{
                                    window.__TAURI_INTERNALS__.invoke('send_window_input', {{
                                        windowId: 'main',
                                        targetId: window._simpleTargetId(target),
                                        value: target.isContentEditable ? target.textContent : target.value
                                    }});
                                }}
                            }});
                            document.addEventListener('change', function(e) {{
                                var target = e.target;
                                var editable = target && target.matches && target.matches('input,textarea,select');
                                if (editable && window.__TAURI_INTERNALS__) {{
                                    var value = target.type === 'checkbox' ? String(!!target.checked) : target.value;
                                    window.__TAURI_INTERNALS__.invoke('send_window_input', {{
                                        windowId: 'main',
                                        targetId: window._simpleTargetId(target),
                                        value: value
                                    }});
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
                    envelope_js,
                    escaped,
                    tauri_mdi_init_script()
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
        SubprocessMessage::OpenWindow {
            window_id,
            title,
            html,
            x,
            y,
            width,
            height,
        } => {
            eprintln!("[tauri-shell] openWindow id={} title={}", window_id, title);
            MDI_OPEN_WINDOW_COUNT.fetch_add(1, Ordering::SeqCst);
            if html.contains("<img") {
                MDI_IMAGE_COUNT.fetch_add(1, Ordering::SeqCst);
            }
            let msg_json = serde_json::json!({
                "type": "openWindow",
                "windowId": window_id,
                "title": title,
                "html": html,
                "x": x,
                "y": y,
                "width": width,
                "height": height
            })
            .to_string();
            eval_tauri_mdi_message(app, msg_json);
            maybe_write_tauri_mdi_proof(app);
        }
        SubprocessMessage::RenderWindow { window_id, html } => {
            let msg_json = serde_json::json!({
                "type": "renderWindow",
                "windowId": window_id,
                "html": html
            })
            .to_string();
            eval_tauri_mdi_message(app, msg_json);
        }
        SubprocessMessage::CloseWindow { window_id } => {
            let msg_json = serde_json::json!({
                "type": "closeWindow",
                "windowId": window_id
            })
            .to_string();
            eval_tauri_mdi_message(app, msg_json);
        }
    }
}

// ---------------------------------------------------------------------------
// Tauri commands
// ---------------------------------------------------------------------------

#[tauri::command]
fn send_keypress(key: String, state: tauri::State<'_, Arc<SimpleProcess>>) {
    state.send(&shell_input_message("key", &key, "", 0.0, 0.0));
}

#[tauri::command]
fn send_window_keypress(
    window_id: String,
    key: String,
    state: tauri::State<'_, Arc<SimpleProcess>>,
) {
    state.send(&ShellMessage::Keypress {
        key,
        window_id: Some(window_id),
    });
}

#[tauri::command]
fn send_action(name: String, state: tauri::State<'_, Arc<SimpleProcess>>) {
    state.send(&shell_input_message("action", "", &name, 0.0, 0.0));
}

#[tauri::command]
fn send_window_action(
    window_id: String,
    name: String,
    state: tauri::State<'_, Arc<SimpleProcess>>,
) {
    state.send(&ShellMessage::Action {
        name,
        window_id: Some(window_id),
    });
}

#[tauri::command]
fn send_window_input(
    window_id: String,
    target_id: String,
    value: String,
    state: tauri::State<'_, Arc<SimpleProcess>>,
) {
    state.send(&shell_input_message_for(
        &window_id, "input", &target_id, "", &value, 0.0, 0.0, 0.0, 0.0, "",
    ));
}

#[tauri::command]
fn send_window_mouse(
    window_id: String,
    kind: String,
    x: f64,
    y: f64,
    button: String,
    state: tauri::State<'_, Arc<SimpleProcess>>,
) {
    state.send(&shell_input_message_for(
        &window_id, &kind, "", "", "", x, y, 0.0, 0.0, &button,
    ));
}

#[tauri::command]
fn send_resize(width: u32, height: u32, state: tauri::State<'_, Arc<SimpleProcess>>) {
    state.send(&shell_input_message(
        "resize",
        "",
        "",
        width as f64,
        height as f64,
    ));
}

#[tauri::command]
fn report_mdi_proof(proof: MdiProof, app: AppHandle) {
    if let Ok(path) = env::var("SIMPLE_TAURI_MDI_PROOF_PATH") {
        let _ = fs::write(path, serde_json::to_string(&proof).unwrap_or_default());
    }
    app.exit(0);
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

fn simple_subprocess_args_for(entry: Option<&str>, shared_wm: bool) -> Vec<String> {
    let mut args = Vec::new();
    if let Some(entry) = entry {
        if entry.ends_with(".ui.sdn") {
            args.extend([
                "run".to_string(),
                "src/app/ui/main.spl".to_string(),
                "tauri".to_string(),
                entry.to_string(),
            ]);
        } else {
            args.extend(["run".to_string(), entry.to_string()]);
        }
    } else if shared_wm {
        args.extend([
            "run".to_string(),
            "src/app/ui/main.spl".to_string(),
            "tauri".to_string(),
        ]);
    }
    if shared_wm {
        args.push("--shared-wm".to_string());
    }
    args
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

fn html_data_url(html: &str) -> String {
    format!("data:text/html;charset=utf-8,{}", urlencoding::encode(html))
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
    let mut initial_url: Option<String> = None;

    // In URL mode, skip subprocess spawning entirely. Shared-WM mode must still
    // spawn the Simple process; otherwise the user only sees a static Rust
    // mockup with no live MDI drag/input bridge.
    if external_url.is_none() {
        let ui_entry = entry_file
            .as_ref()
            .map(|entry| entry.ends_with(".ui.sdn"))
            .unwrap_or(false);

        if let Some(simple_bin) = simple_bin.as_ref() {
            if ui_entry || shared_wm_requested {
                initial_url = Some(html_data_url(mdi_shell_html()));
            }
            {
                let mut cmd = Command::new(simple_bin);
                cmd.args(simple_subprocess_args_for(
                    entry_file.as_deref(),
                    shared_wm_requested,
                ));
                if entry_file
                    .as_ref()
                    .map(|entry| !entry.ends_with(".ui.sdn"))
                    .unwrap_or(false)
                {
                    initial_url = Some(html_data_url(mdi_shell_html()));
                }
                cmd.stdin(Stdio::piped())
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped())
                    .env(
                        "SIMPLE_LIB",
                        env::var("SIMPLE_LIB").unwrap_or_else(|_| "src".to_string()),
                    )
                    .env("SIMPLE_UI_BACKEND", "tauri")
                    .env(
                        "SIMPLE_EXECUTION_MODE",
                        env::var("SIMPLE_EXECUTION_MODE")
                            .unwrap_or_else(|_| "interpret".to_string()),
                    )
                    .env(
                        "SIMPLE_TIMEOUT_SECONDS",
                        env::var("SIMPLE_TIMEOUT_SECONDS").unwrap_or_else(|_| "600".to_string()),
                    );

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
            // No bundled Simple runtime on mobile: the embedded frontendDist
            // (app://index.html) is a complete static render and is the intended
            // UI, so we let it display instead of overlaying a startup error.
            // The diagnostic still goes to stderr/logcat for anyone wiring up a
            // live runtime via SIMPLE_BIN / a bundled runtime / --url.
            eprintln!("[tauri-shell] mobile mode has no bundled Simple binary; showing embedded static UI (set SIMPLE_BIN / a bundled runtime / --url for a live Simple subprocess)");
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
            send_window_keypress,
            send_action,
            send_window_action,
            send_window_input,
            send_window_mouse,
            send_resize,
            report_mdi_proof,
        ])
        .setup(move |app| {
            let url = if let Some(ref ext_url) = external_url {
                eprintln!(
                    "[tauri-shell] creating window with external URL: {}",
                    ext_url
                );
                WebviewUrl::External(ext_url.parse().expect("invalid --url value"))
            } else if let Some(ref initial_url) = initial_url {
                eprintln!("[tauri-shell] creating window from initial data URL");
                WebviewUrl::External(initial_url.parse().expect("invalid initial data URL"))
            } else {
                eprintln!("[tauri-shell] creating window from app://index.html");
                WebviewUrl::App("index.html".into())
            };

            let builder = WebviewWindowBuilder::new(app, "main", url);
            #[cfg(desktop)]
            let builder = builder
                .title("Simple Window Manager")
                .inner_size(1280.0, 720.0);
            let _win = builder.build()?;

            eprintln!("[tauri-shell] window created");

            let stderr_lines: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(Vec::new()));
            let suppress_status_updates = shared_wm_requested;

            if let Some(message) = startup_error.clone() {
                let handle = app.handle().clone();
                thread::spawn(move || {
                    thread::sleep(std::time::Duration::from_millis(500));
                    show_error(&handle, "Startup Error", &message);
                });
            } else {
                if let Some(stdout) = child_stdout {
                    let handle = app.handle().clone();
                    let suppress = suppress_status_updates;
                    thread::spawn(move || {
                        thread::sleep(std::time::Duration::from_millis(500));
                        if !suppress {
                            update_status(
                                &handle,
                                "Waiting for first render from Simple subprocess...",
                            );
                        }
                        read_subprocess_stdout(BufReader::new(stdout), handle, suppress);
                    });
                }
                if let Some(stderr) = child_stderr {
                    let handle = app.handle().clone();
                    let lines = Arc::clone(&stderr_lines);
                    let suppress = suppress_status_updates;
                    thread::spawn(move || {
                        thread::sleep(std::time::Duration::from_millis(500));
                        read_subprocess_stderr(BufReader::new(stderr), handle, lines, suppress);
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
    use super::{
        mdi_shell_html, render_envelope_metadata_js, resolve_simple_binary_from,
        shell_input_message, shell_input_message_for, simple_subprocess_args_for,
        tauri_mdi_init_script, ShellMessage, SubprocessMessage,
    };
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
    fn ui_sdn_launches_live_simple_tauri_runtime() {
        assert_eq!(
            simple_subprocess_args_for(Some("examples/06_io/ui/demo.ui.sdn"), false),
            vec![
                "run".to_string(),
                "src/app/ui/main.spl".to_string(),
                "tauri".to_string(),
                "examples/06_io/ui/demo.ui.sdn".to_string()
            ]
        );
        assert_eq!(
            simple_subprocess_args_for(Some("examples/01_getting_started/hello_native.spl"), false),
            vec![
                "run".to_string(),
                "examples/01_getting_started/hello_native.spl".to_string()
            ]
        );
    }

    #[test]
    fn bundled_runtime_constants_are_absent_without_env() {
        assert!(ANDROID_RUNTIME_AARCH64.is_none() || !ANDROID_RUNTIME_AARCH64.unwrap().is_empty());
        assert!(ANDROID_RUNTIME_X86_64.is_none() || !ANDROID_RUNTIME_X86_64.unwrap().is_empty());
    }

    #[test]
    fn parses_common_render_envelope_fields_from_simple_stdout() {
        let msg: SubprocessMessage = serde_json::from_str(
            r#"{"type":"render","target":"tauri","surface_id":"main","width":640,"height":480,"html":"<main>ok</main>"}"#,
        )
        .expect("common render envelope should parse");

        match msg {
            SubprocessMessage::Render {
                html,
                target,
                surface_id,
                width,
                height,
            } => {
                assert_eq!(target, "tauri");
                assert_eq!(surface_id, "main");
                assert_eq!(width, 640);
                assert_eq!(height, 480);
                assert!(html.contains("<main>ok</main>"));
                let js = render_envelope_metadata_js(&target, &surface_id, width, height);
                assert!(js.contains("target:`tauri`"));
                assert!(js.contains("surface_id:`main`"));
                assert!(js.contains("width:640"));
                assert!(js.contains("height:480"));
            }
            _ => panic!("expected render message"),
        }
    }

    #[test]
    fn serializes_host_events_as_common_input_envelopes() {
        let json = serde_json::to_string(&shell_input_message("key", "Enter", "", 0.0, 0.0))
            .expect("input envelope should serialize");
        assert!(json.contains(r#""type":"input""#));
        assert!(json.contains(r#""target":"tauri""#));
        assert!(json.contains(r#""surface_id":"main""#));
        assert!(json.contains(r#""event_type":"key""#));
        assert!(json.contains(r#""key":"Enter""#));
    }

    #[test]
    fn serializes_mdi_window_scoped_events() {
        let key_json = serde_json::to_string(&ShellMessage::Keypress {
            key: "Enter".to_string(),
            window_id: Some("terminal".to_string()),
        })
        .expect("window keypress should serialize");
        assert!(key_json.contains(r#""type":"keypress""#));
        assert!(key_json.contains(r#""windowId":"terminal""#));
        assert!(key_json.contains(r#""key":"Enter""#));

        let input_json = serde_json::to_string(&shell_input_message_for(
            "terminal",
            "input",
            "proof_input",
            "",
            "ok",
            0.0,
            0.0,
            0.0,
            0.0,
            "",
        ))
        .expect("window input should serialize");
        assert!(input_json.contains(r#""type":"input""#));
        assert!(input_json.contains(r#""surface_id":"terminal""#));
        assert!(input_json.contains(r#""target_id":"proof_input""#));
        assert!(input_json.contains(r#""value":"ok""#));
    }

    #[test]
    fn parses_mdi_window_messages_from_simple_stdout() {
        let msg: SubprocessMessage = serde_json::from_str(
            r#"{"type":"openWindow","windowId":"files","title":"Files","html":"<img class=\"simple-picture\" />","x":10,"y":20,"width":300,"height":200}"#,
        )
        .expect("openWindow envelope should parse");

        match msg {
            SubprocessMessage::OpenWindow {
                window_id,
                title,
                html,
                x,
                y,
                width,
                height,
            } => {
                assert_eq!(window_id, "files");
                assert_eq!(title, "Files");
                assert!(html.contains("simple-picture"));
                assert_eq!(x, 10);
                assert_eq!(y, 20);
                assert_eq!(width, 300);
                assert_eq!(height, 200);
            }
            _ => panic!("expected openWindow message"),
        }
    }

    #[test]
    fn tauri_mdi_bootstrap_has_drag_and_desktop_root() {
        assert!(mdi_shell_html().contains("wm-desktop"));
        let js = tauri_mdi_init_script();
        assert!(js.contains("#wm-desktop{position:fixed;inset:0;overflow:hidden;z-index:10000"));
        assert!(js.contains("pointerdown"));
        assert!(js.contains("pointermove"));
        assert!(js.contains("document.addEventListener('pointermove'"));
        assert!(js.contains("document.addEventListener('pointerup'"));
        assert!(js.contains("document.addEventListener('mousemove'"));
        assert!(js.contains("document.addEventListener('mouseup'"));
        assert!(js.contains("setPointerCapture"));
        assert!(js.contains("releasePointerCapture"));
        assert!(js.contains("bindWindowEvents"));
        assert!(js.contains("send_window_action"));
        assert!(js.contains("send_window_keypress"));
        assert!(js.contains("send_window_input"));
        assert!(js.contains("send_window_mouse"));
        assert!(js.contains("body.tabIndex = 0"));
        assert!(js.contains("bindDrag"));
        assert!(js.contains("notifyMove"));
        assert!(js.contains("wm_move:"));
        assert!(js.contains("simple-tauri-wm-style"));
        let src = include_str!("lib.rs");
        assert!(src.contains(r#".env("SIMPLE_UI_BACKEND", "tauri")"#));
        assert!(src.contains("SIMPLE_EXECUTION_MODE"));
        assert!(src.contains("SIMPLE_TIMEOUT_SECONDS"));
    }
}
