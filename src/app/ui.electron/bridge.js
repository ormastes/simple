// Minimal Electron shell for Simple UI
//
// Launches a BrowserWindow and bridges IPC between the Simple process
// (stdin/stdout JSON) and the Electron renderer (BrowserWindow).
//
// Usage:
//   electron bridge.js [--port PORT]
//   electron bridge.js [--simple-bin ../../bin/simple --entry examples/ui/hello.ui.sdn]
//   electron bridge.js ../../bin/simple examples/ui/hello.ui.sdn

let electron;
try {
    electron = require('electron');
} catch (e) {
    electron = null;
}
const { app, BrowserWindow, ipcMain, dialog, Notification } = electron || {};
const fs = require('fs');
const { spawn } = require('child_process');
const path = require('path');
const {
    commonInputEnvelope,
    renderEnvelopeMetadata,
    renderEnvelopeScript
} = require('./bridge_envelopes.js');

let mainWindow = null;
let simpleProcess = null;

function handleSimpleMessageLine(line, win = mainWindow) {
    try {
        const msg = JSON.parse(line);
        if (msg.type === 'render' && win) {
            const rendered = win.webContents
                .executeJavaScript(renderEnvelopeScript(msg))
                .then(() => win.webContents.executeJavaScript(electronWmInitScript()));
            if (process.env.SIMPLE_ELECTRON_PROOF_PATH) {
                Promise.resolve(rendered)
                    .then(() => win.webContents.executeJavaScript('window.__SIMPLE_WEB_RENDER_ENVELOPE__'))
                    .then(envelope => {
                        fs.writeFileSync(process.env.SIMPLE_ELECTRON_PROOF_PATH, JSON.stringify(envelope));
                        if (app) {
                            app.quit();
                        }
                    })
                    .catch(err => {
                        fs.writeFileSync(process.env.SIMPLE_ELECTRON_PROOF_PATH, JSON.stringify({ error: String(err) }));
                        if (app) {
                            app.quit();
                        }
                    });
            }
            return { handled: true, kind: 'render', envelope: renderEnvelopeMetadata(msg) };
        } else if ((msg.type === 'openWindow' || msg.type === 'renderWindow' || msg.type === 'closeWindow') && win) {
            win.webContents.executeJavaScript(electronWmMessageScript(msg))
                .then(() => maybeWriteMdiProof(win))
                .catch(() => {});
            return { handled: true, kind: msg.type };
        } else if (msg.type === 'dialog' && win) {
            dialog.showMessageBox(win, {
                type: msg.dialogType || 'info',
                title: msg.title || '',
                message: msg.message || ''
            });
            return { handled: true, kind: 'dialog' };
        } else if (msg.type === 'notification') {
            new Notification({ title: msg.title, body: msg.body }).show();
            return { handled: true, kind: 'notification' };
        } else if ((msg.type === 'windowControl' || msg.type === 'window_control') && win) {
            switch (msg.action) {
                case 'minimize': win.minimize(); break;
                case 'maximize': win.isMaximized() ? win.unmaximize() : win.maximize(); break;
                case 'close': win.close(); break;
            }
            return { handled: true, kind: 'windowControl' };
        }
    } catch (e) {
        return { handled: false, kind: 'parse_error' };
    }
    return { handled: false, kind: 'unknown' };
}

function parseCliArgs(argv) {
    const options = {
        port: 3000,
        simpleBin: process.env.SIMPLE_BIN || '',
        entry: process.env.SIMPLE_ENTRY || '',
        url: process.env.SIMPLE_ELECTRON_URL || ''
    };
    const positional = [];
    for (let i = 0; i < argv.length; i++) {
        const arg = argv[i];
        if (arg === '--port' && i + 1 < argv.length) {
            options.port = parseInt(argv[++i], 10);
        } else if (arg === '--simple-bin' && i + 1 < argv.length) {
            options.simpleBin = argv[++i];
        } else if (arg === '--entry' && i + 1 < argv.length) {
            options.entry = argv[++i];
        } else if (arg === '--url' && i + 1 < argv.length) {
            options.url = argv[++i];
        } else if (!arg.startsWith('--')) {
            positional.push(arg);
        }
    }
    if (!options.simpleBin && positional.length > 0) {
        options.simpleBin = positional[0];
    }
    if (!options.entry && positional.length > 1) {
        options.entry = positional[1];
    }
    return options;
}

const options = parseCliArgs(process.argv.slice(2));
const repoRoot = path.resolve(__dirname, '../../..');

function electronAppEntryPath() {
    return path.join(repoRoot, 'src/app/ui.electron/app.spl');
}

function resolveInputPath(input) {
    if (!input || path.isAbsolute(input)) {
        return input;
    }
    const cwdPath = path.resolve(process.cwd(), input);
    if (fs.existsSync(cwdPath)) {
        return cwdPath;
    }
    const repoPath = path.resolve(repoRoot, input);
    if (fs.existsSync(repoPath)) {
        return repoPath;
    }
    return input;
}

function simpleProcessArgs(entry) {
    const resolvedEntry = resolveInputPath(entry);
    if (resolvedEntry.endsWith('.spl')) {
        return ['run', resolvedEntry];
    }
    return ['run', electronAppEntryPath(), resolvedEntry];
}

function startSimpleProcess(simpleBin, entry) {
    if (!simpleBin || !entry) {
        return null;
    }
    const child = spawn(resolveInputPath(simpleBin), simpleProcessArgs(entry), {
        cwd: repoRoot,
        stdio: ['pipe', 'pipe', 'pipe'],
        env: {
            ...process.env,
            SIMPLE_UI_BACKEND: 'electron',
            SIMPLE_EXECUTION_MODE: process.env.SIMPLE_EXECUTION_MODE || 'interpret',
            SIMPLE_TIMEOUT_SECONDS: process.env.SIMPLE_TIMEOUT_SECONDS || '600'
        }
    });
    simpleProcess = child;
    child.stdout.setEncoding('utf8');
    let buffered = '';
    child.stdout.on('data', chunk => {
        buffered += chunk;
        const lines = buffered.split(/\r?\n/);
        buffered = lines.pop() || '';
        for (const line of lines) {
            if (line.trim()) {
                handleSimpleMessage(line);
            }
        }
    });
    child.stderr.setEncoding('utf8');
    child.stderr.on('data', chunk => {
        process.stderr.write(`[simple-electron] ${chunk}`);
    });
    child.on('exit', code => {
        if (mainWindow) {
            mainWindow.webContents.executeJavaScript(`
                window.__SIMPLE_ELECTRON_EXIT_CODE__ = ${Number(code || 0)};
            `).catch(() => {});
        }
    });
    return child;
}

function initialShellHtml() {
    return 'data:text/html;charset=utf-8,' + encodeURIComponent(
        '<!doctype html><html><head><meta charset="utf-8"><title>Simple Electron</title></head><body><div id="app"></div></body></html>'
    );
}

function electronWmInitScript() {
    return `
        (function() {
            if (!document.getElementById('simple-electron-wm-style')) {
                var style = document.createElement('style');
                style.id = 'simple-electron-wm-style';
                style.textContent = '#wm-desktop{position:fixed;inset:0;overflow:hidden;pointer-events:none}.wm-window{position:absolute;display:flex;flex-direction:column;background:#111827;color:#e5e7eb;border:1px solid rgba(255,255,255,.18);box-shadow:0 18px 45px rgba(0,0,0,.42);border-radius:8px;overflow:hidden;pointer-events:auto}.wm-titlebar{height:32px;display:flex;align-items:center;gap:10px;padding:0 10px;background:#0f172a;border-bottom:1px solid rgba(255,255,255,.12);user-select:none;cursor:grab}.wm-titlebar:active{cursor:grabbing}.wm-traffic-lights{display:flex;gap:6px}.wm-traffic-lights button{width:13px;height:13px;border-radius:50%;border:0;font-size:0;padding:0}.wm-traffic-lights button[data-action=close]{background:#ff5f57}.wm-traffic-lights button[data-action=minimize]{background:#febc2e}.wm-traffic-lights button[data-action=maximize]{background:#28c840}.wm-title{font:600 12px system-ui,sans-serif;color:#e5e7eb}.wm-body{flex:1;min-height:0;overflow:hidden;background:#0b0d10}';
                document.head.appendChild(style);
            }
            var desktop = document.getElementById('wm-desktop');
            if (!desktop) {
                desktop = document.createElement('div');
                desktop.id = 'wm-desktop';
                document.body.appendChild(desktop);
            }
            if (!window.__SIMPLE_ELECTRON_WM__) {
                window.__SIMPLE_ELECTRON_WM__ = {
                    windows: {},
                    z: 20,
                    drag: null,
                    bindDrag: function(id, win, titlebar) {
                        var self = this;
                        titlebar.addEventListener('pointerdown', function(ev) {
                            if (ev.target && ev.target.closest && ev.target.closest('button')) return;
                            self.focus(id);
                            var rect = win.getBoundingClientRect();
                            self.drag = {
                                id: id,
                                win: win,
                                pointerId: ev.pointerId,
                                startX: ev.clientX,
                                startY: ev.clientY,
                                left: rect.left,
                                top: rect.top
                            };
                            titlebar.setPointerCapture(ev.pointerId);
                            ev.preventDefault();
                        });
                        titlebar.addEventListener('pointermove', function(ev) {
                            var drag = self.drag;
                            if (!drag || drag.id !== id || drag.pointerId !== ev.pointerId) return;
                            var nextLeft = Math.max(0, drag.left + ev.clientX - drag.startX);
                            var nextTop = Math.max(0, drag.top + ev.clientY - drag.startY);
                            win.style.left = nextLeft + 'px';
                            win.style.top = nextTop + 'px';
                        });
                        titlebar.addEventListener('pointerup', function(ev) {
                            if (self.drag && self.drag.pointerId === ev.pointerId) {
                                self.drag = null;
                                try { titlebar.releasePointerCapture(ev.pointerId); } catch (_) {}
                                self.notifyMove(id, win);
                            }
                        });
                        titlebar.addEventListener('pointercancel', function(ev) {
                            if (self.drag && self.drag.pointerId === ev.pointerId) self.drag = null;
                        });
                    },
                    focus: function(id) {
                        var existing = this.windows[id];
                        if (!existing) return;
                        existing.win.style.zIndex = String(++this.z);
                    },
                    notifyMove: function(id, win) {
                        var left = parseInt(win.style.left || '0', 10) || 0;
                        var top = parseInt(win.style.top || '0', 10) || 0;
                        if (window.simpleElectron && window.simpleElectron.sendInput) {
                            window.simpleElectron.sendInput({
                                type: 'input',
                                target: 'electron',
                                surface_id: id,
                                event_type: 'action',
                                target_id: '',
                                key: '',
                                value: 'wm_move:' + id + ':' + left + ':' + top,
                                x: left,
                                y: top,
                                dx: 0,
                                dy: 0,
                                button: ''
                            });
                        }
                    },
                    receiveElectronMessage: function(msg) {
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
                                body.innerHTML = msg.html || '';
                                titlebar.appendChild(lights);
                                titlebar.appendChild(title);
                                win.appendChild(titlebar);
                                win.appendChild(body);
                                desktop.appendChild(win);
                                existing = this.windows[id] = { win: win, body: body, title: title };
                                this.bindDrag(id, win, titlebar);
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
    `;
}

function electronWmMessageScript(msg) {
    return electronWmInitScript() + `
        window.__SIMPLE_ELECTRON_WM__.receiveElectronMessage(${JSON.stringify(msg)});
        ({
            count: Object.keys(window.__SIMPLE_ELECTRON_WM__.windows || {}).length,
            text: document.body.innerText,
            html: document.body.innerHTML
        });
    `;
}

function maybeWriteMdiProof(win) {
    if (!process.env.SIMPLE_ELECTRON_MDI_PROOF_PATH || !win) {
        return;
    }
    win.webContents.executeJavaScript(`
        (function() {
            var wm = window.__SIMPLE_ELECTRON_WM__;
            var dragMoved = false;
            var dragBefore = null;
            var dragAfter = null;
            if (wm && wm.windows && wm.windows.terminal) {
                var terminal = wm.windows.terminal.win;
                var titlebar = terminal.querySelector('.wm-titlebar');
                dragBefore = { left: parseInt(terminal.style.left || '0', 10) || 0, top: parseInt(terminal.style.top || '0', 10) || 0 };
                if (titlebar && typeof PointerEvent === 'function') {
                    titlebar.dispatchEvent(new PointerEvent('pointerdown', { pointerId: 37, clientX: dragBefore.left + 12, clientY: dragBefore.top + 12, bubbles: true }));
                    titlebar.dispatchEvent(new PointerEvent('pointermove', { pointerId: 37, clientX: dragBefore.left + 72, clientY: dragBefore.top + 42, bubbles: true }));
                    titlebar.dispatchEvent(new PointerEvent('pointerup', { pointerId: 37, clientX: dragBefore.left + 72, clientY: dragBefore.top + 42, bubbles: true }));
                }
                dragAfter = { left: parseInt(terminal.style.left || '0', 10) || 0, top: parseInt(terminal.style.top || '0', 10) || 0 };
                dragMoved = dragAfter.left > dragBefore.left && dragAfter.top > dragBefore.top;
            }
            return {
            count: window.__SIMPLE_ELECTRON_WM__ ? Object.keys(window.__SIMPLE_ELECTRON_WM__.windows || {}).length : 0,
            text: document.body.innerText,
            hasDesktop: !!document.getElementById('wm-desktop'),
            imageCount: document.querySelectorAll('img.simple-picture').length,
            hasDragRuntime: !!(window.__SIMPLE_ELECTRON_WM__ && window.__SIMPLE_ELECTRON_WM__.bindDrag),
            hasDragEvents: !!(window.__SIMPLE_ELECTRON_WM__ && window.__SIMPLE_ELECTRON_WM__.notifyMove),
            dragMoved: dragMoved,
            dragBefore: dragBefore,
            dragAfter: dragAfter,
            htmlRenderable: document.body.innerHTML.indexOf('simple-app-window') >= 0 && document.body.innerHTML.indexOf('<pre class="simple-app-pre">') >= 0
            };
        })();
    `).then(proof => {
        fs.writeFileSync(process.env.SIMPLE_ELECTRON_MDI_PROOF_PATH, JSON.stringify(proof));
        if (proof.count >= 4 && app) {
            app.quit();
        }
    }).catch(err => {
        fs.writeFileSync(process.env.SIMPLE_ELECTRON_MDI_PROOF_PATH, JSON.stringify({ error: String(err) }));
    });
}

function shellUrl() {
    if (options.url) {
        return options.url;
    }
    if (options.simpleBin && options.entry) {
        return initialShellHtml();
    }
    return `http://localhost:${options.port}`;
}

if (app) app.whenReady().then(() => {
    const platform = process.platform;

    const winOptions = {
        width: 1280,
        height: 720,
        titleBarStyle: platform === 'darwin' ? 'hiddenInset' : 'hidden',
        titleBarOverlay: platform !== 'darwin'
            ? { color: '#0b0d10', symbolColor: '#ffffff', height: 28 }
            : undefined,
        backgroundColor: '#0b0d10',
        webPreferences: {
            nodeIntegration: false,
            contextIsolation: true,
            preload: path.join(__dirname, 'preload.js')
        },
        title: 'Simple UI'
    };

    // Platform-specific material support
    if (platform === 'darwin') {
        winOptions.vibrancy = 'sidebar';
    }
    if (platform === 'win32') {
        winOptions.backgroundMaterial = 'mica';
    }

    mainWindow = new BrowserWindow(winOptions);

    mainWindow.loadURL(shellUrl());
    mainWindow.webContents.once('did-finish-load', () => {
        startSimpleProcess(options.simpleBin, options.entry);
    });

    // Forward window events to Simple process
    mainWindow.on('resize', () => {
        const [width, height] = mainWindow.getContentSize();
        sendToSimple(commonInputEnvelope('resize', { x: width, y: height }));
    });

    mainWindow.on('closed', () => {
        mainWindow = null;
        sendToSimple(commonInputEnvelope('quit'));
        if (simpleProcess) {
            simpleProcess.kill();
            simpleProcess = null;
        }
    });
});

// IPC handlers for native features
if (ipcMain) ipcMain.handle('show-dialog', async (event, options) => {
    const result = await dialog.showMessageBox(mainWindow, options);
    return result;
});

if (ipcMain) ipcMain.handle('show-open-dialog', async (event, options) => {
    const result = await dialog.showOpenDialog(mainWindow, options);
    return result;
});

if (ipcMain) ipcMain.handle('show-save-dialog', async (event, options) => {
    const result = await dialog.showSaveDialog(mainWindow, options);
    return result;
});

if (ipcMain) ipcMain.handle('show-notification', async (event, { title, body }) => {
    new Notification({ title, body }).show();
});

if (ipcMain) ipcMain.on('simple-input', (event, envelope) => {
    sendToSimple(envelope);
});

// Stdin/stdout IPC with Simple process
function sendToSimple(msg) {
    if (simpleProcess && simpleProcess.stdin.writable) {
        simpleProcess.stdin.write(JSON.stringify(msg) + '\n');
    }
}

// Handle messages from Simple process (stdout)
function handleSimpleMessage(line) {
    handleSimpleMessageLine(line, mainWindow);
}

if (app) app.on('window-all-closed', () => {
    app.quit();
});

module.exports = {
    commonInputEnvelope,
    electronWmInitScript,
    handleSimpleMessageLine,
    parseCliArgs,
    renderEnvelopeMetadata,
    renderEnvelopeScript,
    simpleProcessArgs
};
