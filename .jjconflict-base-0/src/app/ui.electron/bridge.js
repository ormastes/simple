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
let mdiProofInputFrames = [];

function handleSimpleMessageLine(line, win = mainWindow) {
    try {
        const msg = JSON.parse(line);
        if (msg.type === 'render' && win) {
            const rendered = win.webContents
                .executeJavaScript(renderEnvelopeScript(msg))
                .then(() => win.webContents.executeJavaScript(electronWmInitScript()));
            if (process.env.SIMPLE_ELECTRON_PROOF_PATH) {
                Promise.resolve(rendered)
                    .then(() => win.webContents.executeJavaScript(electronLiveSmokeProofScript()))
                    .then(envelope => attachElectronLiveSmokeScreenshot(win, envelope))
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
        } else if (msg.type === 'fileDialog' && win) {
            runFileDialog(win, msg.dialogType || 'open', msg.filters || '')
                .then(result => sendToSimple({ type: 'fileDialogResult', canceled: result.canceled, paths: result.canceled ? '' : result.paths }))
                .catch(err => sendToSimple({ type: 'fileDialogResult', canceled: true, paths: '', error: String(err && err.message ? err.message : err) }));
            return { handled: true, kind: 'fileDialog' };
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

// Parse the comma-separated extension list the Simple side sends for
// open/save dialogs (e.g. "spl,txt") into Electron's `filters` shape.
// Empty input means "no filter" (all files).
function parseDialogFilters(filters) {
    const extensions = String(filters || '').split(',').map(s => s.trim()).filter(Boolean);
    if (extensions.length === 0) {
        return [];
    }
    return [{ name: 'Files', extensions }];
}

// Invoke the real Electron file dialog (open or save) and normalize the
// result to { canceled, paths } — `paths` is newline-joined selected
// path(s), empty when the user cancels. Never returns success without
// actually calling dialog.showOpenDialog/showSaveDialog.
function runFileDialog(win, dialogType, filters) {
    const filterSpec = parseDialogFilters(filters);
    if (dialogType === 'save') {
        return dialog.showSaveDialog(win, { filters: filterSpec }).then(result => ({
            canceled: !!result.canceled,
            paths: result.canceled || !result.filePath ? '' : result.filePath
        }));
    }
    return dialog.showOpenDialog(win, { properties: ['openFile'], filters: filterSpec }).then(result => ({
        canceled: !!result.canceled,
        paths: result.canceled ? '' : (result.filePaths || []).join('\n')
    }));
}

function bitmapEvidence(bitmap) {
    let checksum = 0;
    let nonTransparent = 0;
    const distinct = new Set();
    for (let index = 0; index + 3 < bitmap.length; index += 4) {
        const b = bitmap[index];
        const g = bitmap[index + 1];
        const r = bitmap[index + 2];
        const a = bitmap[index + 3];
        checksum = (checksum + ((r + 1) * 3) + ((g + 1) * 5) + ((b + 1) * 7) + ((a + 1) * 11) + index) >>> 0;
        if (a !== 0) {
            nonTransparent += 1;
        }
        if (distinct.size < 4096) {
            distinct.add(`${r},${g},${b},${a}`);
        }
    }
    return {
        checksum,
        nonTransparent,
        distinctColorCount: distinct.size
    };
}

function attachElectronLiveSmokeScreenshot(win, envelope) {
    const screenshotPath = process.env.SIMPLE_ELECTRON_SCREENSHOT_PATH || '';
    if (!screenshotPath || !win || !win.webContents) {
        return Promise.resolve(Object.assign({}, envelope, {
            screenshot_path: '',
            screenshot_error: 'missing-screenshot-path'
        }));
    }
    const resolvedScreenshotPath = path.resolve(screenshotPath);
    return win.webContents.capturePage().then(image => {
        const png = image.toPNG();
        const bitmap = image.toBitmap();
        const size = image.getSize();
        const pixels = bitmapEvidence(bitmap);
        fs.mkdirSync(path.dirname(resolvedScreenshotPath), { recursive: true });
        fs.writeFileSync(resolvedScreenshotPath, png);
        return Object.assign({}, envelope, {
            screenshot_path: resolvedScreenshotPath,
            screenshot_width: size.width,
            screenshot_height: size.height,
            screenshot_png_size_bytes: png.length,
            screenshot_bitmap_byte_count: bitmap.length,
            screenshot_pixel_checksum: pixels.checksum,
            screenshot_nontransparent_pixel_count: pixels.nonTransparent,
            screenshot_distinct_color_count: pixels.distinctColorCount,
            screenshot_error: ''
        });
    }).catch(err => Object.assign({}, envelope, {
        screenshot_path: resolvedScreenshotPath,
        screenshot_error: String(err && err.message ? err.message : err)
    }));
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

function electronLiveSmokeProofScript() {
    return `
        new Promise(function(resolve) {
            try {
            var envelope = window.__SIMPLE_WEB_RENDER_ENVELOPE__ || {};
            var appEl = document.getElementById('app');
            var performanceNowAvailable = !!(window.performance && typeof window.performance.now === 'function');
            var start = performanceNowAvailable ? window.performance.now() : 0;
            var animationFrameAvailable = typeof window.requestAnimationFrame === 'function';
            var frameCount = 0;
            var eventProbeType = 'simple-electron-live-smoke-event';
            var eventProbeDetail = 'live-smoke-input';
            var eventDispatchAvailable = typeof document.addEventListener === 'function' && typeof document.dispatchEvent === 'function' && (typeof window.CustomEvent === 'function' || typeof document.createEvent === 'function');
            var eventDispatchCount = 0;
            var eventDispatchObservedType = '';
            var eventDispatchObservedDetail = '';
            var eventDispatchError = '';
            var eventDispatchStartMs = null;
            function eventProbeHandler(event) {
                eventDispatchCount += 1;
                eventDispatchObservedType = event.type || '';
                eventDispatchObservedDetail = event.detail && event.detail.kind ? String(event.detail.kind) : '';
            }
            try {
                document.addEventListener(eventProbeType, eventProbeHandler);
                if (eventDispatchAvailable) {
                    var eventProbe = null;
                    if (typeof window.CustomEvent === 'function') {
                        eventProbe = new CustomEvent(eventProbeType, {
                            detail: { kind: eventProbeDetail }
                        });
                    } else {
                        eventProbe = document.createEvent('CustomEvent');
                        eventProbe.initCustomEvent(eventProbeType, false, false, { kind: eventProbeDetail });
                    }
                    eventDispatchStartMs = performanceNowAvailable ? window.performance.now() : null;
                    document.dispatchEvent(eventProbe);
                }
            } catch (eventProbeErr) {
                eventDispatchError = String(eventProbeErr && eventProbeErr.message ? eventProbeErr.message : eventProbeErr);
            } finally {
                document.removeEventListener(eventProbeType, eventProbeHandler);
            }
            var styleProbe = document.createElement('style');
            styleProbe.textContent = '@keyframes simple-electron-live-smoke-pulse { from { opacity: 0.2; } to { opacity: 0.9; } } .simple-electron-live-smoke-animation { animation: simple-electron-live-smoke-pulse 80ms linear 2; }';
            document.head.appendChild(styleProbe);
            var animationProbe = document.createElement('div');
            animationProbe.className = 'simple-electron-live-smoke-animation';
            animationProbe.style.cssText = 'position:fixed;left:-1000px;top:-1000px;width:8px;height:8px;';
            document.body.appendChild(animationProbe);
            function finish() {
                try {
                var style = window.getComputedStyle(animationProbe);
                var text = appEl ? (appEl.textContent || '') : '';
                var userAgent = (window.navigator && window.navigator.userAgent) || '';
                var runtimeVersions = window.simpleElectron && typeof window.simpleElectron.runtimeVersions === 'function'
                    ? window.simpleElectron.runtimeVersions()
                    : {};
                var eventDispatchToPaintMs = performanceNowAvailable && eventDispatchStartMs !== null
                    ? Math.max(0, window.performance.now() - eventDispatchStartMs)
                    : null;
                var proof = Object.assign({}, envelope, {
                    proof_source: 'src/app/ui.electron/bridge.js:electronLiveSmokeProofScript',
                    browser_engine: new RegExp('Chrome/|Chromium/').test(userAgent) ? 'chromium' : '',
                    electron_user_agent: userAgent,
                    electron_process_version: runtimeVersions.electron || '',
                    chrome_process_version: runtimeVersions.chrome || '',
                    app_element_present: !!appEl,
                    body_text_length: text.length,
                    body_text_sample: text.slice(0, 120),
                    performance_now_available: performanceNowAvailable,
                    performance_now_delta_ms: performanceNowAvailable ? Math.max(0, window.performance.now() - start) : null,
                    animation_frame_available: animationFrameAvailable,
                    animation_frame_count: frameCount,
                    css_animation_probe: style.animationName === 'simple-electron-live-smoke-pulse',
                    event_dispatch_available: eventDispatchAvailable,
                    event_dispatch_count: eventDispatchCount,
                    event_dispatch_type: eventDispatchObservedType,
                    event_dispatch_detail: eventDispatchObservedDetail,
                    event_dispatch_error: eventDispatchError,
                    event_dispatch_to_paint_ms: eventDispatchToPaintMs,
                    blur_or_tolerance_used: false
                });
                animationProbe.remove();
                styleProbe.remove();
                resolve(proof);
                } catch (finishErr) {
                    resolve({
                        error: String(finishErr && finishErr.message ? finishErr.message : finishErr),
                        stack: finishErr && finishErr.stack ? String(finishErr.stack) : ''
                    });
                }
            }
            if (animationFrameAvailable) {
                requestAnimationFrame(function() {
                    frameCount += 1;
                    requestAnimationFrame(function() {
                        frameCount += 1;
                        finish();
                    });
                });
            } else {
                finish();
            }
            } catch (proofErr) {
                resolve({
                    error: String(proofErr && proofErr.message ? proofErr.message : proofErr),
                    stack: proofErr && proofErr.stack ? String(proofErr.stack) : ''
                });
            }
        })
    `;
}

function electronWmInitScript() {
    return `
        (function() {
            if (!document.getElementById('simple-electron-wm-style')) {
                var style = document.createElement('style');
                style.id = 'simple-electron-wm-style';
                style.textContent = '#wm-desktop{position:fixed;inset:0;overflow:hidden;isolation:isolate}#wm-desktop .wm-window{position:absolute;display:flex;flex-direction:column;overflow:hidden}#wm-desktop .wm-body{flex:1;min-height:0;overflow:auto}#wm-desktop .wm-titlebar{display:flex;align-items:center;gap:8px;height:46px;padding:0 18px;background:linear-gradient(180deg,rgba(255,255,255,.12),rgba(255,255,255,.04));border-bottom:1px solid rgba(255,255,255,.12);user-select:none;cursor:grab}#wm-desktop .wm-titlebar:active{cursor:grabbing}#wm-desktop .wm-title{font:600 13px/1 var(--ui-font-label,system-ui,sans-serif);color:var(--ui-text,#e5e7eb);flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}#wm-desktop .wm-titlebar-widgets{display:flex;align-items:center;gap:6px;margin-left:auto}#wm-desktop .wm-titlebar-widgets [data-simple-titlebar-widget]{min-height:24px}';
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
                    dragEventsBound: false,
                    lastEvent: null,
                    elementId: function(el) {
                        if (!el) return '';
                        return el.getAttribute('data-target-id') || el.getAttribute('data-widget-id') || el.getAttribute('data-id') || el.id || el.name || '';
                    },
                    sendWindowEvent: function(id, eventType, fields) {
                        var payload = Object.assign({
                            type: 'input',
                            target: 'electron',
                            surface_id: id,
                            event_type: eventType,
                            target_id: '',
                            key: '',
                            value: '',
                            x: 0,
                            y: 0,
                            dx: 0,
                            dy: 0,
                            button: ''
                        }, fields || {});
                        if (window.simpleElectron && window.simpleElectron.sendInput) {
                            window.simpleElectron.sendInput(payload);
                        }
                    },
                    sendWindowAction: function(id, action) {
                        this.lastEvent = { kind: 'action', windowId: id, action: action };
                        this.sendWindowEvent(id, 'action', { value: action });
                    },
                    sendWindowKey: function(id, key) {
                        this.lastEvent = { kind: 'key', windowId: id, key: key };
                        this.sendWindowEvent(id, 'key', { key: key });
                    },
                    sendWindowInput: function(id, targetId, value) {
                        this.lastEvent = { kind: 'input', windowId: id, targetId: targetId, value: value };
                        this.sendWindowEvent(id, 'input', { target_id: targetId, value: value });
                    },
                    sendWindowMouse: function(id, kind, ev) {
                        var rect = this.windows[id] && this.windows[id].body ? this.windows[id].body.getBoundingClientRect() : { left: 0, top: 0 };
                        this.lastEvent = { kind: kind, windowId: id };
                        this.sendWindowEvent(id, kind, {
                            x: ev.clientX - rect.left,
                            y: ev.clientY - rect.top,
                            button: ev.button === 2 ? 'right' : (ev.button === 1 ? 'middle' : 'left')
                        });
                    },
                    mountTitlebarWidgets: function(existing) {
                        if (!existing || !existing.titlebar || !existing.body) return;
                        var old = existing.titlebar.querySelector('.wm-titlebar-widgets');
                        if (old) old.remove();
                        var source = Array.from(existing.body.querySelectorAll('[data-simple-titlebar-widget]'));
                        if (!source.length) return;
                        var slot = document.createElement('div');
                        slot.className = 'wm-titlebar-widgets';
                        source.forEach(function(widget) {
                            var clone = widget.cloneNode(true);
                            clone.removeAttribute('id');
                            slot.appendChild(clone);
                        });
                        existing.titlebar.appendChild(slot);
                    },
                    bindGlobalDragEvents: function() {
                        var self = this;
                        if (self.dragEventsBound) return;
                        self.dragEventsBound = true;
                        document.addEventListener('pointermove', function(ev) {
                            self.moveDrag(ev, ev.pointerId, false);
                        });
                        document.addEventListener('pointerup', function(ev) {
                            self.finishDrag(ev, ev.pointerId, false);
                        });
                        document.addEventListener('pointercancel', function(ev) {
                            self.cancelDrag(ev.pointerId, false);
                        });
                        document.addEventListener('mousemove', function(ev) {
                            self.moveDrag(ev, 'mouse', true);
                        });
                        document.addEventListener('mouseup', function(ev) {
                            self.finishDrag(ev, 'mouse', true);
                        });
                    },
                    isDragControl: function(ev) {
                        if (ev.target && ev.target.closest && ev.target.closest('button')) return true;
                        return false;
                    },
                    beginDrag: function(id, win, ev, pointerId, isMouse) {
                        if (this.isDragControl(ev)) return false;
                        this.focus(id);
                        var rect = win.getBoundingClientRect();
                        var styleLeft = parseInt(win.style.left || '', 10);
                        var styleTop = parseInt(win.style.top || '', 10);
                        this.drag = {
                            id: id,
                            win: win,
                            pointerId: pointerId,
                            mouse: !!isMouse,
                            startX: ev.clientX,
                            startY: ev.clientY,
                            left: isNaN(styleLeft) ? rect.left : styleLeft,
                            top: isNaN(styleTop) ? rect.top : styleTop
                        };
                        ev.preventDefault();
                        return true;
                    },
                    moveDrag: function(ev, pointerId, isMouse) {
                        var drag = this.drag;
                        if (!drag || drag.pointerId !== pointerId || drag.mouse !== !!isMouse) return;
                        var nextLeft = Math.max(0, drag.left + ev.clientX - drag.startX);
                        var nextTop = Math.max(0, drag.top + ev.clientY - drag.startY);
                        drag.win.style.left = nextLeft + 'px';
                        drag.win.style.top = nextTop + 'px';
                        ev.preventDefault();
                    },
                    finishDrag: function(ev, pointerId, isMouse) {
                        var drag = this.drag;
                        if (!drag || drag.pointerId !== pointerId || drag.mouse !== !!isMouse) return;
                        this.drag = null;
                        this.notifyMove(drag.id, drag.win);
                    },
                    cancelDrag: function(pointerId, isMouse) {
                        if (this.drag && this.drag.pointerId === pointerId && this.drag.mouse === !!isMouse) this.drag = null;
                    },
                    bindDrag: function(id, win, titlebar) {
                        var self = this;
                        self.bindGlobalDragEvents();
                        titlebar.addEventListener('pointerdown', function(ev) {
                            if (!self.beginDrag(id, win, ev, ev.pointerId, false)) return;
                            try { titlebar.setPointerCapture(ev.pointerId); } catch (_) {}
                        });
                        titlebar.addEventListener('pointermove', function(ev) {
                            self.moveDrag(ev, ev.pointerId, false);
                        });
                        titlebar.addEventListener('pointerup', function(ev) {
                            try { titlebar.releasePointerCapture(ev.pointerId); } catch (_) {}
                            self.finishDrag(ev, ev.pointerId, false);
                        });
                        titlebar.addEventListener('pointercancel', function(ev) {
                            self.cancelDrag(ev.pointerId, false);
                        });
                        titlebar.addEventListener('mousedown', function(ev) {
                            if (ev.button !== 0) return;
                            self.beginDrag(id, win, ev, 'mouse', true);
                        });
                        titlebar.addEventListener('mousemove', function(ev) {
                            self.moveDrag(ev, 'mouse', true);
                        });
                        titlebar.addEventListener('mouseup', function(ev) {
                            self.finishDrag(ev, 'mouse', true);
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
                        this.lastEvent = { kind: 'action', windowId: id, action: 'wm_move:' + id + ':' + left + ':' + top };
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
                        win.addEventListener('keydown', function(ev) {
                            var key = ev.key || '';
                            if (key.length === 1 || ['Enter','Escape','Backspace','Tab','ArrowUp','ArrowDown','ArrowLeft','ArrowRight'].indexOf(key) >= 0) {
                                self.sendWindowKey(id, key);
                            }
                        });
                        win.addEventListener('input', function(ev) {
                            var target = ev.target;
                            var editable = target && ((target.matches && target.matches('input,textarea,select')) || target.isContentEditable);
                            if (!editable) return;
                            self.sendWindowInput(id, self.elementId(target), target.isContentEditable ? target.textContent : target.value);
                        });
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
                                existing = this.windows[id] = { win: win, body: body, title: title, titlebar: titlebar };
                                this.bindDrag(id, win, titlebar);
                                this.bindWindowEvents(id, win, body);
                            } else {
                                existing.body.innerHTML = msg.html || '';
                                existing.title.textContent = msg.title || id;
                            }
                            this.mountTitlebarWidgets(existing);
                            this.focus(id);
                        } else if (msg.type === 'renderWindow' && this.windows[msg.windowId]) {
                            this.windows[msg.windowId].body.innerHTML = msg.html || '';
                            this.mountTitlebarWidgets(this.windows[msg.windowId]);
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
    mdiProofInputFrames = [];
    win.webContents.executeJavaScript(`
            (async function() {
                var wm = window.__SIMPLE_ELECTRON_WM__;
                var performanceNowAvailable = !!(window.performance && typeof window.performance.now === 'function');
                var performanceStart = performanceNowAvailable ? window.performance.now() : 0;
                var inputToPaintStart = 0;
                var inputToPaintMs = 0;
                var animationFrameAvailable = typeof window.requestAnimationFrame === 'function';
                var animationFrameCount = 0;
                var styleProbe = document.createElement('style');
                styleProbe.textContent = '@keyframes simple-electron-mdi-proof-pulse { from { opacity: 0.2; } to { opacity: 0.9; } } .simple-electron-mdi-proof-animation { animation: simple-electron-mdi-proof-pulse 120ms linear 2; }';
                document.head.appendChild(styleProbe);
                var animationProbe = document.createElement('div');
                animationProbe.className = 'simple-electron-mdi-proof-animation';
                animationProbe.style.cssText = 'position:fixed;left:-1000px;top:-1000px;width:8px;height:8px;';
                document.body.appendChild(animationProbe);
                if (animationFrameAvailable) {
                    await new Promise(function(resolve) {
                        requestAnimationFrame(function() {
                            animationFrameCount += 1;
                            requestAnimationFrame(function() {
                                animationFrameCount += 1;
                                resolve();
                            });
                        });
                    });
                }
                var animationProbeStyle = window.getComputedStyle(animationProbe);
                var dragMoved = false;
                var bodyClickRouted = false;
                var bodyInputRouted = false;
                var bodyKeyRouted = false;
                var trafficMinimizeRouted = false;
                var trafficMaximizeRouted = false;
                var trafficCloseRouted = false;
                var eventSequence = [];
                var appActionControlFound = false;
                var appInputControlFound = false;
                var dragBefore = null;
                var dragAfter = null;
                var taskbarItems = Array.from(document.querySelectorAll('#dock .tab-bar-item'));
                var taskbarIcons = Array.from(document.querySelectorAll('#dock .tab-bar-icon'));
                var taskbarIconsVisible = taskbarIcons.length >= 4 && taskbarIcons.every(function(icon) {
                    var rect = icon.getBoundingClientRect();
                    var style = window.getComputedStyle(icon);
                    return rect.width >= 18 && rect.height >= 18 && style.display !== 'none' && style.visibility !== 'hidden' && style.opacity !== '0';
                });
                var taskbarLabelsVisible = taskbarItems.length >= 4 && taskbarItems.every(function(item) {
                    var label = item.querySelector('.tab-bar-label');
                    if (!label) return false;
                    var rect = label.getBoundingClientRect();
                    var style = window.getComputedStyle(label);
                    return rect.width >= 20 && rect.height >= 10 && style.display !== 'none' && style.visibility !== 'hidden' && style.opacity !== '0';
                });
                if (wm && wm.windows && wm.windows.terminal) {
                    inputToPaintStart = performanceNowAvailable ? window.performance.now() : 0;
                    var terminal = wm.windows.terminal.win;
                    var body = wm.windows.terminal.body;
                    var titlebar = terminal.querySelector('.wm-titlebar');
                    dragBefore = { left: parseInt(terminal.style.left || '0', 10) || 0, top: parseInt(terminal.style.top || '0', 10) || 0 };
                if (titlebar && typeof PointerEvent === 'function') {
                    titlebar.dispatchEvent(new PointerEvent('pointerdown', { pointerId: 37, pointerType: 'mouse', isPrimary: true, button: 0, buttons: 1, clientX: dragBefore.left + 12, clientY: dragBefore.top + 12, bubbles: true }));
                    titlebar.dispatchEvent(new PointerEvent('pointermove', { pointerId: 37, pointerType: 'mouse', isPrimary: true, button: 0, buttons: 1, clientX: dragBefore.left + 72, clientY: dragBefore.top + 42, bubbles: true }));
                    document.dispatchEvent(new PointerEvent('pointerup', { pointerId: 37, pointerType: 'mouse', isPrimary: true, button: 0, buttons: 0, clientX: dragBefore.left + 72, clientY: dragBefore.top + 42, bubbles: true }));
                    }
                    dragAfter = { left: parseInt(terminal.style.left || '0', 10) || 0, top: parseInt(terminal.style.top || '0', 10) || 0 };
                    dragMoved = dragAfter.left > dragBefore.left && dragAfter.top > dragBefore.top;
                    if (titlebar && !dragMoved) {
                        titlebar.dispatchEvent(new MouseEvent('mousedown', { button: 0, buttons: 1, clientX: dragBefore.left + 12, clientY: dragBefore.top + 12, bubbles: true }));
                        titlebar.dispatchEvent(new MouseEvent('mousemove', { button: 0, buttons: 1, clientX: dragBefore.left + 72, clientY: dragBefore.top + 42, bubbles: true }));
                        document.dispatchEvent(new MouseEvent('mouseup', { button: 0, buttons: 0, clientX: dragBefore.left + 72, clientY: dragBefore.top + 42, bubbles: true }));
                        dragAfter = { left: parseInt(terminal.style.left || '0', 10) || 0, top: parseInt(terminal.style.top || '0', 10) || 0 };
                        dragMoved = dragAfter.left > dragBefore.left && dragAfter.top > dragBefore.top;
                    }
                    if (dragMoved) {
                        eventSequence.push('window_drag:move');
                    }
                    if (body) {
                        var appButton = body.querySelector('[data-action]');
                        appActionControlFound = !!appButton;
                        if (appButton) {
                            var actionName = appButton.getAttribute('data-action') || '';
                            if (typeof PointerEvent === 'function') {
                                appButton.dispatchEvent(new PointerEvent('pointerdown', { pointerId: 41, pointerType: 'mouse', isPrimary: true, button: 0, buttons: 1, clientX: 20, clientY: 20, bubbles: true }));
                                appButton.dispatchEvent(new PointerEvent('pointerup', { pointerId: 41, pointerType: 'mouse', isPrimary: true, button: 0, buttons: 0, clientX: 20, clientY: 20, bubbles: true }));
                            }
                            appButton.dispatchEvent(new MouseEvent('click', { bubbles: true }));
                            bodyClickRouted = !!(wm.lastEvent && wm.lastEvent.kind === 'action' && wm.lastEvent.windowId === 'terminal' && wm.lastEvent.action === actionName);
                            if (bodyClickRouted) {
                                eventSequence.push('app_action:body_click');
                            }
                        }

                        var appInput = body.querySelector('input[data-target-id]:not([data-simple-titlebar-widget]), textarea[data-target-id]:not([data-simple-titlebar-widget]), select[data-target-id]:not([data-simple-titlebar-widget]), [contenteditable][data-target-id]:not([data-simple-titlebar-widget])');
                        appInputControlFound = !!appInput;
                        if (appInput) {
                            var targetId = appInput.getAttribute('data-target-id') || appInput.id || '';
                            if (appInput.isContentEditable) {
                                appInput.textContent = 'ok';
                            } else {
                                appInput.value = 'ok';
                            }
                            appInput.dispatchEvent(new Event('input', { bubbles: true }));
                            bodyInputRouted = !!(wm.lastEvent && wm.lastEvent.kind === 'input' && wm.lastEvent.windowId === 'terminal' && wm.lastEvent.targetId === targetId && wm.lastEvent.value === 'ok');
                            if (bodyInputRouted) {
                                eventSequence.push('app_input:body_input');
                            }
                        }
                        body.dispatchEvent(new KeyboardEvent('keydown', { key: 'Enter', bubbles: true }));
                        bodyKeyRouted = !!(wm.lastEvent && wm.lastEvent.kind === 'key' && wm.lastEvent.windowId === 'terminal' && wm.lastEvent.key === 'Enter');
                        if (bodyKeyRouted) {
                            eventSequence.push('app_key:body_key');
                        }
                    }
                    var minimizeButton = terminal.querySelector('.wm-traffic-lights [data-action="minimize"]');
                    var maximizeButton = terminal.querySelector('.wm-traffic-lights [data-action="maximize"]');
                    if (minimizeButton) {
                        minimizeButton.dispatchEvent(new MouseEvent('click', { bubbles: true, cancelable: true }));
                        trafficMinimizeRouted = !!(wm.lastEvent && wm.lastEvent.kind === 'action' && wm.lastEvent.windowId === 'terminal' && wm.lastEvent.action === 'minimize');
                    }
                    if (maximizeButton) {
                        maximizeButton.dispatchEvent(new MouseEvent('click', { bubbles: true, cancelable: true }));
                        trafficMaximizeRouted = !!(wm.lastEvent && wm.lastEvent.kind === 'action' && wm.lastEvent.windowId === 'terminal' && wm.lastEvent.action === 'maximize');
                    }
                    wm.receiveElectronMessage({
                        type: 'openWindow',
                        windowId: 'bridge-proof-close',
                        title: 'Bridge Close Proof',
                        appId: 'proof',
                        x: 24,
                        y: 24,
                        width: 180,
                        height: 120,
                        html: '<button data-action="proof_body_action">Proof</button>'
                    });
                    var closeWin = wm.windows['bridge-proof-close'] && wm.windows['bridge-proof-close'].win;
                    var closeButton = closeWin ? closeWin.querySelector('.wm-traffic-lights [data-action="close"]') : null;
                    if (closeButton) {
                        closeButton.dispatchEvent(new MouseEvent('click', { bubbles: true, cancelable: true }));
                        trafficCloseRouted = !!(wm.lastEvent && wm.lastEvent.kind === 'action' && wm.lastEvent.windowId === 'bridge-proof-close' && wm.lastEvent.action === 'close' && !wm.windows['bridge-proof-close']);
                    }
                }
                if (inputToPaintStart > 0 && animationFrameAvailable) {
                    await new Promise(function(resolve) {
                        requestAnimationFrame(function() {
                            requestAnimationFrame(resolve);
                        });
                    });
                }
                inputToPaintMs = performanceNowAvailable && inputToPaintStart > 0 ? Math.max(0, window.performance.now() - inputToPaintStart) : 0;
                return {
            count: window.__SIMPLE_ELECTRON_WM__ ? Object.keys(window.__SIMPLE_ELECTRON_WM__.windows || {}).length : 0,
            text: document.body.innerText,
            hasDesktop: !!document.getElementById('wm-desktop'),
            imageCount: document.querySelectorAll('img.simple-picture').length,
            hasDragRuntime: !!(window.__SIMPLE_ELECTRON_WM__ && window.__SIMPLE_ELECTRON_WM__.bindDrag),
            hasDragEvents: !!(window.__SIMPLE_ELECTRON_WM__ && window.__SIMPLE_ELECTRON_WM__.notifyMove),
            dragMoved: dragMoved,
            hasWindowEventRuntime: !!(wm && wm.bindWindowEvents && wm.sendWindowAction && wm.sendWindowInput && wm.sendWindowMouse),
            appActionControlFound: appActionControlFound,
            appInputControlFound: appInputControlFound,
            bodyClickRouted: bodyClickRouted,
            bodyInputRouted: bodyInputRouted,
            bodyKeyRouted: bodyKeyRouted,
            eventSequence: eventSequence,
            trafficMinimizeRouted: trafficMinimizeRouted,
            trafficMaximizeRouted: trafficMaximizeRouted,
            trafficCloseRouted: trafficCloseRouted,
            taskbarItemCount: taskbarItems.length,
            taskbarIconCount: taskbarIcons.length,
            taskbarIconsVisible: taskbarIconsVisible,
            taskbarLabelsVisible: taskbarLabelsVisible,
            dragBefore: dragBefore,
            dragAfter: dragAfter,
            htmlRenderable: document.body.innerHTML.indexOf('simple-app-window') >= 0 && document.body.innerHTML.indexOf('<pre class="simple-app-pre">') >= 0,
            performanceNowAvailable: performanceNowAvailable,
            performanceNowDeltaMs: performanceNowAvailable ? Math.max(0, window.performance.now() - performanceStart) : null,
            inputToPaintMs: inputToPaintMs,
            animationFrameAvailable: animationFrameAvailable,
            animationFrameCount: animationFrameCount,
            cssAnimationProbe: animationProbeStyle.animationName === 'simple-electron-mdi-proof-pulse'
            };
        })();
    `).then(proof => {
        const screenshotPath = process.env.SIMPLE_ELECTRON_MDI_SCREENSHOT_PATH || '';
        const finish = () => {
            proof.bridgeInputFrames = mdiProofInputFrames.slice();
            proof.bridgeIpcFrameCount = proof.bridgeInputFrames.length;
            proof.bridgeBodyActionFrameRouted = proof.bridgeInputFrames.some(frame => frame && frame.surface_id === 'terminal' && frame.event_type === 'action' && frame.value === 'mdi_terminal_action');
            proof.bridgeBodyInputFrameRouted = proof.bridgeInputFrames.some(frame => frame && frame.surface_id === 'terminal' && frame.event_type === 'input' && frame.target_id === 'mdi_terminal_input' && frame.value === 'ok');
            proof.bridgeBodyKeyFrameRouted = proof.bridgeInputFrames.some(frame => frame && frame.surface_id === 'terminal' && frame.event_type === 'key' && frame.key === 'Enter');
            proof.bridgeMouseDownFrameRouted = proof.bridgeInputFrames.some(frame => frame && frame.surface_id === 'terminal' && frame.event_type === 'mouse_down');
            proof.bridgeMouseUpFrameRouted = proof.bridgeInputFrames.some(frame => frame && frame.surface_id === 'terminal' && frame.event_type === 'mouse_up');
            proof.bridgeMinimizeFrameRouted = proof.bridgeInputFrames.some(frame => frame && frame.surface_id === 'terminal' && frame.event_type === 'action' && frame.value === 'minimize');
            proof.bridgeMaximizeFrameRouted = proof.bridgeInputFrames.some(frame => frame && frame.surface_id === 'terminal' && frame.event_type === 'action' && frame.value === 'maximize');
            proof.bridgeCloseFrameRouted = proof.bridgeInputFrames.some(frame => frame && frame.surface_id === 'bridge-proof-close' && frame.event_type === 'action' && frame.value === 'close');
            fs.writeFileSync(process.env.SIMPLE_ELECTRON_MDI_PROOF_PATH, JSON.stringify(proof));
            if (proof.count >= 4 && app) {
                app.quit();
            }
        };
        if (screenshotPath) {
            win.webContents.capturePage().then(image => {
                fs.mkdirSync(path.dirname(screenshotPath), { recursive: true });
                fs.writeFileSync(screenshotPath, image.toPNG());
                proof.screenshotPath = screenshotPath;
                setTimeout(finish, 50);
            }).catch(err => {
                proof.screenshotError = String(err);
                setTimeout(finish, 50);
            });
        } else {
            setTimeout(finish, 50);
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

    // When a SIMPLE_ELECTRON_TITLE is provided (e.g. the web-render backend
    // comparison), use a standard visible title bar so the title — which names
    // the backend — is actually shown. The WM/MDI default hides it (hiddenInset).
    const showTitle = !!process.env.SIMPLE_ELECTRON_TITLE;
    const winOptions = {
        width: Number(process.env.SIMPLE_ELECTRON_WIDTH) || 1280,
        height: Number(process.env.SIMPLE_ELECTRON_HEIGHT) || 720,
        titleBarStyle: showTitle ? 'default' : (platform === 'darwin' ? 'hiddenInset' : 'hidden'),
        titleBarOverlay: (!showTitle && platform !== 'darwin')
            ? { color: '#0b0d10', symbolColor: '#ffffff', height: 28 }
            : undefined,
        backgroundColor: '#0b0d10',
        webPreferences: {
            nodeIntegration: false,
            contextIsolation: true,
            preload: path.join(__dirname, 'preload.js')
        },
        title: process.env.SIMPLE_ELECTRON_TITLE || 'Simple UI'
    };

    // Platform-specific material support
    if (platform === 'darwin') {
        winOptions.vibrancy = 'sidebar';
    }
    if (platform === 'win32') {
        winOptions.backgroundMaterial = 'mica';
    }

    mainWindow = new BrowserWindow(winOptions);

    // Lock the window title to our backend label: a loaded page's <title>
    // (document.title) otherwise overrides it, hiding which backend rendered.
    if (process.env.SIMPLE_ELECTRON_TITLE) {
        const lockedTitle = process.env.SIMPLE_ELECTRON_TITLE;
        mainWindow.on('page-title-updated', (e) => { e.preventDefault(); });
        mainWindow.setTitle(lockedTitle);
        mainWindow.webContents.on('did-finish-load', () => mainWindow.setTitle(lockedTitle));
    }

    // Optional zoom (e.g. 0.25 = 4x smaller fonts) for the web-render comparison.
    const zoomFactor = Number(process.env.SIMPLE_ELECTRON_ZOOM);
    if (zoomFactor > 0) {
        mainWindow.webContents.on('did-finish-load', () => {
            mainWindow.webContents.setZoomFactor(zoomFactor);
        });
    }

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
    if (process.env.SIMPLE_ELECTRON_MDI_PROOF_PATH) {
        mdiProofInputFrames.push(envelope);
    }
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
    electronLiveSmokeProofScript,
    electronWmInitScript,
    handleSimpleMessageLine,
    parseCliArgs,
    renderEnvelopeMetadata,
    renderEnvelopeScript,
    simpleProcessArgs
};
