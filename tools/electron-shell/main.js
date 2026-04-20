// Electron main process for Simple Language UI
//
// Spawns a Simple binary as a subprocess and bridges JSON IPC
// between the Simple process (stdin/stdout) and the Electron renderer.
//
// Usage:
//   electron . <entry.spl>
//   SIMPLE_BIN=/path/to/simple electron . <entry.spl>

const { app, BrowserWindow, ipcMain, dialog, Notification, net } = require('electron');
const { spawn } = require('child_process');
const path = require('path');
const fs = require('fs');
const os = require('os');

let mainWindow = null;
let simpleProcess = null;
let lineBuffer = '';
let nativeSmokeFrames = [];
let nativeSmokeStarted = false;
// childWindows/webContentsToWindowId were used by the old openWindow
// handler that spawned separate BrowserWindow instances. The WM now
// runs in the main renderer (wm.js) so there are no child BrowserWindows.
const webContentsToWindowId = new Map();  // webContents.id → windowId (main only)
const debugLogPath = '/tmp/simple-ui-captures/electron-shell-debug.log';
const dumpHtmlPath = process.env.SIMPLE_UI_DUMP_HTML_PATH || '';
const projectRoot = path.resolve(__dirname, '..', '..');

function isNativeSmokeMode() {
    return process.argv.includes('--smoke-native-window') || process.env.SIMPLE_ELECTRON_NATIVE_SMOKE === '1';
}

function debugLog(message) {
    const line = `[${new Date().toISOString()}] ${message}\n`;
    try {
        fs.appendFileSync(debugLogPath, line);
    } catch (err) {
        // Best-effort logging only.
    }
}

function dumpRenderedHtml(html) {
    if (!dumpHtmlPath) return;
    try {
        fs.mkdirSync(path.dirname(dumpHtmlPath), { recursive: true });
        fs.writeFileSync(dumpHtmlPath, html, 'utf8');
        debugLog(`dumped html to ${dumpHtmlPath}`);
    } catch (err) {
        debugLog(`failed to dump html: ${err.message}`);
    }
}

function browserWindowMap() {
    if (!global.simpleBrowserWindows) global.simpleBrowserWindows = new Map();
    return global.simpleBrowserWindows;
}

function normalizeWindowId(windowId) {
    if (windowId === null || windowId === undefined) return '';
    return String(windowId);
}

function getNativeWindow(windowId) {
    return browserWindowMap().get(normalizeWindowId(windowId));
}

function readNativeWindowBounds(bw) {
    if (!bw || bw.isDestroyed()) return null;
    try {
        const [x, y] = bw.getPosition();
        const [width, height] = bw.getSize();
        return { x, y, width, height };
    } catch (err) {
        debugLog(`readNativeWindowBounds failed: ${err.message}`);
        return null;
    }
}

function buildNativeWindowEvent(type, windowId, bw, extra = {}) {
    const normalizedWindowId = normalizeWindowId(windowId);
    const payload = {
        type,
        windowId: normalizedWindowId
    };
    if (bw && !bw.isDestroyed()) {
        payload.bounds = readNativeWindowBounds(bw);
        payload.title = bw.getTitle();
        payload.minimized = bw.isMinimized();
        payload.maximized = bw.isMaximized();
        payload.visible = bw.isVisible();
    }
    return { ...payload, ...extra };
}

function emitNativeWindowEvent(type, windowId, bw, extra = {}) {
    if (mainWindow && !mainWindow.isDestroyed()) {
        mainWindow.webContents.send(
            'native-window-event',
            buildNativeWindowEvent(type, windowId, bw, extra)
        );
    }
}

function resolveNativeWindowUrl(rawUrl) {
    const url = String(rawUrl || '');
    if (/^[a-zA-Z]+:\/\//.test(url)) return url;
    if (mainWindow && !mainWindow.isDestroyed()) {
        try {
            return new URL(url, mainWindow.webContents.getURL()).toString();
        } catch (err) {
            debugLog(`resolveNativeWindowUrl failed for ${url}: ${err.message}`);
        }
    }
    return url || 'about:blank';
}

function registerNativeWindowEvents(windowId, bw) {
    const normalizedWindowId = normalizeWindowId(windowId);
    bw.on('focus', () => emitNativeWindowEvent('focus', normalizedWindowId, bw));
    bw.on('minimize', () => emitNativeWindowEvent('minimize', normalizedWindowId, bw));
    bw.on('restore', () => emitNativeWindowEvent('restore', normalizedWindowId, bw));
    bw.on('maximize', () => emitNativeWindowEvent('maximize', normalizedWindowId, bw));
    bw.on('unmaximize', () => emitNativeWindowEvent('unmaximize', normalizedWindowId, bw));
    bw.on('move', () => emitNativeWindowEvent('move', normalizedWindowId, bw));
    bw.on('resize', () => emitNativeWindowEvent('resize', normalizedWindowId, bw));
    bw.on('page-title-updated', (event, title) => {
        emitNativeWindowEvent('title', normalizedWindowId, bw, { title });
    });
    bw.on('closed', () => {
        browserWindowMap().delete(normalizedWindowId);
        emitNativeWindowEvent('close', normalizedWindowId);
    });
}

function spawnNativeWindow({ windowId, url, width, height, title }) {
    const map = browserWindowMap();
    const normalizedWindowId = normalizeWindowId(windowId);
    const existing = map.get(normalizedWindowId);
    if (existing && !existing.isDestroyed()) {
        existing.focus();
        return true;
    }
    const bw = new BrowserWindow({
        width: width || 800,
        height: height || 600,
        title: title || 'Simple App',
        show: true,
        webPreferences: {
            nodeIntegration: false,
            contextIsolation: true
        }
    });
    bw.loadURL(resolveNativeWindowUrl(url));
    registerNativeWindowEvents(normalizedWindowId, bw);
    map.set(normalizedWindowId, bw);
    debugLog(`spawned BrowserWindow windowId=${normalizedWindowId} url=${url}`);
    return true;
}

function closeNativeWindow(windowId) {
    const map = browserWindowMap();
    const normalizedWindowId = normalizeWindowId(windowId);
    const bw = map.get(normalizedWindowId);
    if (!bw || bw.isDestroyed()) {
        map.delete(normalizedWindowId);
        return false;
    }
    bw.close();
    map.delete(normalizedWindowId);
    debugLog(`closed BrowserWindow windowId=${normalizedWindowId}`);
    return true;
}

function focusNativeWindow(windowId) {
    const bw = getNativeWindow(windowId);
    if (!bw || bw.isDestroyed()) return false;
    bw.show();
    bw.focus();
    return true;
}

function minimizeNativeWindow(windowId) {
    const bw = getNativeWindow(windowId);
    if (!bw || bw.isDestroyed()) return false;
    bw.minimize();
    return true;
}

function restoreNativeWindow(windowId) {
    const bw = getNativeWindow(windowId);
    if (!bw || bw.isDestroyed()) return false;
    if (bw.isMinimized()) bw.restore();
    bw.show();
    bw.focus();
    return true;
}

function moveNativeWindow(windowId, x, y) {
    const bw = getNativeWindow(windowId);
    if (!bw || bw.isDestroyed()) return false;
    const [currentX, currentY] = bw.getPosition();
    const nextX = Number.isFinite(Number(x)) ? Number(x) : currentX;
    const nextY = Number.isFinite(Number(y)) ? Number(y) : currentY;
    bw.setPosition(nextX, nextY);
    return true;
}

function resizeNativeWindow(windowId, width, height) {
    const bw = getNativeWindow(windowId);
    if (!bw || bw.isDestroyed()) return false;
    const [currentWidth, currentHeight] = bw.getSize();
    const nextWidth = Number.isFinite(Number(width)) ? Number(width) : currentWidth;
    const nextHeight = Number.isFinite(Number(height)) ? Number(height) : currentHeight;
    bw.setSize(nextWidth, nextHeight);
    return true;
}

function maximizeNativeWindow(windowId) {
    const bw = getNativeWindow(windowId);
    if (!bw || bw.isDestroyed()) return false;
    if (bw.isMinimized()) bw.restore();
    bw.maximize();
    return true;
}

function unmaximizeNativeWindow(windowId) {
    const bw = getNativeWindow(windowId);
    if (!bw || bw.isDestroyed()) return false;
    if (!bw.isMaximized()) return true;
    bw.unmaximize();
    return true;
}

function setNativeWindowTitle(windowId, title) {
    const bw = getNativeWindow(windowId);
    if (!bw || bw.isDestroyed()) return false;
    bw.setTitle(String(title || ''));
    emitNativeWindowEvent('title', windowId, bw, { title: bw.getTitle() });
    return true;
}

// Resolve Simple binary path: CLI arg --bin, env SIMPLE_BIN, or default.
// The deployed self-hosted bin/simple currently has a dispatch fallthrough
// bug (#3 in doc/08_tracking/bug/wm_cocoa_session_findings_2026-04-15.md)
// where `bin/simple <file.spl>` always returns "Error running" exit 1.
// Until that lands, prefer the Rust seed bootstrap binary when present —
// it runs `.spl` files reliably.
function resolveSimpleBin() {
    const args = process.argv.slice(2);
    for (let i = 0; i < args.length; i++) {
        if (args[i] === '--bin' && i + 1 < args.length) {
            return args[i + 1];
        }
    }
    if (process.env.SIMPLE_BIN) {
        return process.env.SIMPLE_BIN;
    }
    const projectRoot = path.join(__dirname, '..', '..');
    const seedBin = path.join(projectRoot, 'src', 'compiler_rust', 'target', 'bootstrap', 'simple');
    if (fs.existsSync(seedBin)) {
        return seedBin;
    }
    return path.join(projectRoot, 'bin', 'simple');
}

// Collect non-flag arguments as the entry file and its args.
// Strips Electron/CDP flags (--bin, --remote-debugging-port, etc.)
// so they don't leak into the Simple subprocess command line.
function resolveEntryArgs() {
    const args = process.argv.slice(2);
    const result = [];
    let skipNext = false;
    for (let i = 0; i < args.length; i++) {
        if (skipNext) {
            skipNext = false;
            continue;
        }
        if (args[i] === '--bin') {
            skipNext = true;
            continue;
        }
        // Filter out Electron/Chromium flags injected by the CDP launcher
        if (args[i].startsWith('--remote-debugging-port')) {
            continue;
        }
        if (args[i] === '--smoke-native-window') {
            continue;
        }
        if (args[i] === '--') {
            continue;
        }
        result.push(args[i]);
    }
    return result;
}

// Send a JSON message to the Simple subprocess stdin
function sendToSimple(msg) {
    if (simpleProcess && simpleProcess.stdin.writable) {
        simpleProcess.stdin.write(JSON.stringify(msg) + '\n');
    }
}

// Fetch a URL via Electron's net module and ship the body back to Simple as
// a `fetch_result` message. Handles redirects automatically. Supports the
// hosted browser's minimal GET/POST path. Body is capped at 256 KB to keep
// the IPC payload under the parse_ipc_message ceiling (we'll truncate; for
// v1 that's fine).
const FETCH_BODY_CAP = 256 * 1024;
function parseHeaderBlock(headerText) {
    const out = [];
    for (const rawLine of String(headerText || '').split('\n')) {
        const line = rawLine.trim();
        if (!line) continue;
        const idx = line.indexOf(':');
        if (idx <= 0) continue;
        out.push([line.slice(0, idx).trim(), line.slice(idx + 1).trim()]);
    }
    return out;
}

function serializeResponseHeaders(headers) {
    const lines = [];
    for (const [name, value] of Object.entries(headers || {})) {
        if (Array.isArray(value)) {
            for (const item of value) {
                lines.push(`${name}: ${item}`);
            }
        } else if (value !== undefined && value !== null) {
            lines.push(`${name}: ${String(value)}`);
        }
    }
    return lines.join('\n');
}

function handleFetchRequest(url, requestId, method = 'GET', headers = '', body = '', contentType = '') {
    const normalizedMethod = String(method || 'GET').toUpperCase();
    debugLog(`request_fetch method=${normalizedMethod} url=${url} requestId=${requestId} bodyBytes=${Buffer.byteLength(String(body || ''), 'utf8')}`);
    if (!url) {
        sendToSimple({ type: 'fetch_result', requestId, url: '', status: 0, headers: '', body: '', error: 'empty url' });
        return;
    }
    let request;
    try {
        request = net.request({ method: normalizedMethod, url, redirect: 'follow' });
    } catch (err) {
        sendToSimple({ type: 'fetch_result', requestId, url, status: 0, headers: '', body: '', error: String(err.message || err) });
        return;
    }
    for (const [name, value] of parseHeaderBlock(headers)) {
        request.setHeader(name, value);
    }
    const bodyText = String(body || '');
    if (bodyText && contentType) {
        request.setHeader('Content-Type', contentType);
    }
    let chunks = [];
    let total = 0;
    let truncated = false;
    request.on('response', (response) => {
        const status = response.statusCode || 0;
        response.on('data', (chunk) => {
            if (truncated) return;
            const remaining = FETCH_BODY_CAP - total;
            if (chunk.length > remaining) {
                chunks.push(chunk.slice(0, remaining));
                total += remaining;
                truncated = true;
            } else {
                chunks.push(chunk);
                total += chunk.length;
            }
        });
        response.on('end', () => {
            const body = Buffer.concat(chunks).toString('utf8');
            const responseHeaders = serializeResponseHeaders(response.headers);
            sendToSimple({
                type: 'fetch_result',
                requestId,
                url,
                status: String(status),
                headers: responseHeaders,
                body,
                error: truncated ? `truncated at ${FETCH_BODY_CAP} bytes` : ''
            });
        });
    });
    request.on('error', (err) => {
        debugLog(`request_fetch error method=${normalizedMethod} url=${url} err=${err.message}`);
        sendToSimple({ type: 'fetch_result', requestId, url, status: 0, headers: '', body: '', error: String(err.message || err) });
    });
    if (bodyText) {
        request.write(bodyText);
    }
    request.end();
}

// Handle a single JSON line from the Simple subprocess stdout
function handleSimpleMessage(line) {
    if (!line.trim()) return;
    try {
        const msg = JSON.parse(line);
        if (msg && msg.t) {
            if (mainWindow && !mainWindow.isDestroyed()) {
                mainWindow.webContents.send('wm-frame', msg);
                debugLog(`forwarded wm frame t=${msg.t}`);
            }
            return;
        }
        debugLog(`ipc message type=${msg.type || 'unknown'}`);
        switch (msg.type) {
            case 'render':
                if (mainWindow) {
                    dumpRenderedHtml(msg.html || '');
                    mainWindow.webContents.send('render', msg.html);
                }
                break;

            // Canvas2D paint commands from a Simple-side renderer (e.g. the
            // Blink-style pipeline at src/lib/blink/). The renderer-side
            // executor in index.html iterates ops and calls the matching
            // Canvas2D APIs.
            case 'paint_canvas':
                if (mainWindow && !mainWindow.isDestroyed()) {
                    mainWindow.webContents.send('paint-canvas', {
                        ops: Array.isArray(msg.ops) ? msg.ops : [],
                        width: msg.width || 0,
                        height: msg.height || 0
                    });
                }
                break;

            // HTTP fetch on behalf of the Simple subprocess. Done in the main
            // process via Electron's net module — no CSP, no SFFI dependency.
            // Result is shipped back to Simple's stdin as a `fetch_result`
            // message that parse_ipc_message decodes into UIEvent.FetchResult.
            case 'request_fetch':
                handleFetchRequest(
                    msg.url || '',
                    msg.requestId || '',
                    msg.method || 'GET',
                    msg.headers || '',
                    msg.body || '',
                    msg.contentType || ''
                );
                break;

            case 'notification':
                if (Notification.isSupported()) {
                    new Notification({
                        title: msg.title || '',
                        body: msg.body || ''
                    }).show();
                }
                break;

            case 'dialog':
                if (mainWindow) {
                    dialog.showMessageBox(mainWindow, {
                        type: msg.dialog_type || 'info',
                        title: msg.title || '',
                        message: msg.message || ''
                    });
                }
                break;

            // Window manager messages — previously these created separate
            // BrowserWindow instances floating OUTSIDE the main window. They
            // are now forwarded to the main renderer so SimpleWindowManager
            // (src/app/ui.web/wm.js, symlinked here as wm.js) draws them as
            // floating divs INSIDE the main Electron window.
            case 'openWindow':
            case 'closeWindow':
            case 'renderWindow':
            case 'moveWindow':
            case 'resizeWindow':
            case 'focusWindow':
            case 'minimizeWindow':
                if (mainWindow && !mainWindow.isDestroyed()) {
                    mainWindow.webContents.send('wm-message', msg);
                    debugLog(`forwarded wm message type=${msg.type} id=${msg.windowId || '-'}`);
                    if (msg.type === 'openWindow') {
                        sendToSimple({ type: 'windowOpened', windowId: msg.windowId });
                    }
                }
                break;

            // Wave 5: spawn a real top-level BrowserWindow and load a URL.
            // Contract paired with src/app/ui.electron/backend.spl:
            //   new_browser_window(window_id, url, w, h, title).
            // Windows are tracked in `simpleBrowserWindows` keyed by windowId
            // so close_browser_window can later destroy them.
            case 'new_browser_window':
                try {
                    spawnNativeWindow({
                        windowId: msg.windowId,
                        url: msg.url,
                        width: msg.width,
                        height: msg.height,
                        title: msg.title
                    });
                } catch (err) {
                    debugLog(`new_browser_window failed: ${err.message}`);
                }
                break;
            case 'close_browser_window':
                try {
                    closeNativeWindow(msg.windowId);
                } catch (err) {
                    debugLog(`close_browser_window failed: ${err.message}`);
                }
                break;

            case 'windowControl':
            case 'window_control':
                if (mainWindow) {
                    switch (msg.action) {
                        case 'minimize':
                            mainWindow.minimize();
                            break;
                        case 'maximize':
                            if (mainWindow.isMaximized()) {
                                mainWindow.unmaximize();
                            } else {
                                mainWindow.maximize();
                            }
                            break;
                        case 'close':
                            mainWindow.close();
                            break;
                    }
                }
                break;

            default:
                // Unknown message type; ignore
                break;
        }
    } catch (e) {
        // Non-JSON output from the subprocess; ignore
        debugLog(`non-json stdout: ${line}`);
    }
}

// Spawn the Simple binary subprocess
function spawnSimpleProcess() {
    const bin = resolveSimpleBin();
    const entryArgs = resolveEntryArgs();

    if (entryArgs.length === 0) {
        // Default to the hello_electron .spl entry when no entry file is given
        // (e.g. when launched via play_launch for CDP automation).
        // Use the .spl file (not .ui.sdn) because it goes through run_electron()
        // which handles Electron IPC directly.
        const defaultSpl = path.join(projectRoot, 'examples', 'ui', 'hello_electron.spl');
        if (fs.existsSync(defaultSpl)) {
            debugLog('no entry args — falling back to hello_electron.spl');
            entryArgs.push(defaultSpl);
        } else {
            debugLog('no entry args provided');
            console.error('Usage: electron . <entry.spl> [args...]');
            console.error('  --bin <path>   Path to Simple binary (or set SIMPLE_BIN)');
            app.quit();
            return;
        }
    }

    const commandArgs = entryArgs.length > 0 && entryArgs[0].endsWith('.ui.sdn')
        ? ['ui', 'electron', ...entryArgs]
        : ['run', ...entryArgs];

    simpleProcess = spawn(bin, commandArgs, {
        stdio: ['pipe', 'pipe', 'pipe'],
        cwd: projectRoot,
        env: {
            ...process.env,
            SIMPLE_UI_BACKEND: 'electron',
            SIMPLE_ELECTRON_PLATFORM: process.platform,
            SIMPLE_HOME: projectRoot,
            SIMPLE_TIMEOUT_SECONDS: '0',
            SIMPLE_EXAMPLE_ISOLATED_CHILD: '1'
        }
    });
    debugLog(`spawned simple pid=${simpleProcess.pid || 'unknown'} bin=${bin} args=${commandArgs.join(' ')}`);

    // Read stdout line by line
    simpleProcess.stdout.on('data', (data) => {
        lineBuffer += data.toString();
        const lines = lineBuffer.split('\n');
        // Keep the last incomplete line in the buffer
        lineBuffer = lines.pop();
        for (const line of lines) {
            handleSimpleMessage(line);
        }
    });

    simpleProcess.stderr.on('data', (data) => {
        debugLog(`stderr: ${data.toString().trim()}`);
        process.stderr.write(data);
    });

    simpleProcess.on('close', (code) => {
        debugLog(`simple process closed code=${code}`);
        simpleProcess = null;
        if (code !== 0 && code !== null) {
            console.error(`Simple process exited with code ${code}`);
        }
        if (mainWindow && !mainWindow.isDestroyed()) {
            mainWindow.webContents.send(
                'render',
                '<div style="padding:24px;color:#ff6b6b"><h2>Simple process exited</h2><p>The Electron shell is still open so logs remain visible.</p></div>'
            );
        }
    });

    simpleProcess.on('error', (err) => {
        debugLog(`simple process start error: ${err.message}`);
        console.error(`Failed to start Simple process: ${err.message}`);
        dialog.showErrorBox(
            'Simple Process Error',
            `Could not start Simple binary at: ${bin}\n\n${err.message}`
        );
        app.quit();
    });
}

function waitMs(ms) {
    return new Promise((resolve) => setTimeout(resolve, ms));
}

function nativeSmokeCommandKinds() {
    return nativeSmokeFrames.map((frame) => {
        const payload = frame && frame.payload ? frame.payload : {};
        return payload.cmd_type || payload.kind || '';
    }).filter(Boolean);
}

function nativeSmokeHasKind(kind) {
    return nativeSmokeCommandKinds().includes(kind);
}

async function runNativeWindowSmoke() {
    if (nativeSmokeStarted) return;
    nativeSmokeStarted = true;
    const windowId = 'simple-electron-smoke-window';
    nativeSmokeFrames = [];
    try {
        await waitMs(250);
        spawnNativeWindow({
            windowId,
            url: 'data:text/html,<title>Smoke Window</title><body>Simple Electron smoke</body>',
            width: 420,
            height: 280,
            title: 'Smoke Window'
        });
        await waitMs(200);
        focusNativeWindow(windowId);
        await waitMs(150);
        minimizeNativeWindow(windowId);
        await waitMs(200);
        restoreNativeWindow(windowId);
        await waitMs(200);
        moveNativeWindow(windowId, 40, 40);
        await waitMs(200);
        resizeNativeWindow(windowId, 460, 300);
        await waitMs(200);
        setNativeWindowTitle(windowId, 'Smoke Window Updated');
        await waitMs(200);
        closeNativeWindow(windowId);
        await waitMs(250);

        const required = ['focus', 'minimize', 'restore', 'move', 'resize', 'set_title', 'close'];
        const missing = required.filter((kind) => !nativeSmokeHasKind(kind));
        if (missing.length > 0) {
            console.error(`Electron native smoke failed; missing native feedback: ${missing.join(', ')}`);
            console.error(`Observed feedback: ${nativeSmokeCommandKinds().join(', ') || '(none)'}`);
            app.exit(1);
            return;
        }
        console.log(`Electron native smoke passed: ${nativeSmokeCommandKinds().join(', ')}`);
        app.exit(0);
    } catch (err) {
        console.error(`Electron native smoke failed: ${err.stack || err.message || err}`);
        app.exit(1);
    }
}

// Create the main window and start the subprocess
app.whenReady().then(() => {
    debugLog('app.whenReady');
    const isMac = process.platform === 'darwin';
    const isWin = process.platform === 'win32';
    mainWindow = new BrowserWindow({
        width: 1360,
        height: 840,
        minWidth: 1024,
        minHeight: 640,
        // Stitch Obsidian neutral override #060612 — matches glass_obsidian_dark()
        backgroundColor: isMac ? '#00000000' : '#060612',
        transparent: isMac,
        show: false,
        titleBarStyle: isMac ? 'hiddenInset' : 'default',
        trafficLightPosition: isMac ? { x: 16, y: 14 } : undefined,
        vibrancy: isMac ? 'under-window' : undefined,
        visualEffectState: isMac ? 'active' : undefined,
        hasShadow: true,
        webPreferences: {
            nodeIntegration: false,
            contextIsolation: true,
            preload: path.join(__dirname, 'preload.js')
        },
        title: 'Simple UI'
    });
    debugLog('browser window created');

    if (isMac) {
        mainWindow.setWindowButtonVisibility(true);
    }

    if (isWin) {
        const buildPart = parseInt(os.release().split('.')[2] || '0', 10);
        if (buildPart >= 22000) {
            try {
                mainWindow.setBackgroundMaterial('mica');
            } catch (err) {
                debugLog(`setBackgroundMaterial(mica) failed: ${err.message}`);
            }
        }
    }

    mainWindow.loadFile(path.join(__dirname, 'index.html'));
    debugLog('loadFile(index.html) requested');

    mainWindow.once('ready-to-show', () => {
        if (mainWindow && !mainWindow.isDestroyed()) {
            debugLog('window ready-to-show');
            mainWindow.show();
        }
    });

    mainWindow.webContents.on('did-finish-load', () => {
        debugLog('window did-finish-load');
        webContentsToWindowId.set(mainWindow.webContents.id, 'main');
        if (isNativeSmokeMode()) {
            runNativeWindowSmoke();
        }
    });
    mainWindow.webContents.on('render-process-gone', (event, details) => {
        debugLog(`render-process-gone reason=${details.reason}`);
    });
    mainWindow.webContents.on('did-fail-load', (event, code, desc) => {
        debugLog(`did-fail-load code=${code} desc=${desc}`);
    });

    // Forward resize events to the Simple process
    mainWindow.on('resize', () => {
        const [width, height] = mainWindow.getContentSize();
        debugLog(`window resize ${width}x${height}`);
        sendToSimple({ type: 'resize', width, height });
    });

    mainWindow.on('closed', () => {
        debugLog('window closed');
        mainWindow = null;
    });

    if (!isNativeSmokeMode()) {
        spawnSimpleProcess();
    }
});

// IPC from renderer: keypress (tagged with windowId)
ipcMain.on('wm-frame-to-simple', (event, frame) => {
    if (isNativeSmokeMode()) {
        nativeSmokeFrames.push(frame || {});
        debugLog(`smoke captured wm frame t=${(frame && frame.t) || ''}`);
        return;
    }
    sendToSimple(frame || {});
});

ipcMain.on('keypress', (event, key) => {
    const windowId = webContentsToWindowId.get(event.sender.id) || 'main';
    debugLog(`keypress key=${JSON.stringify(key)} windowId=${windowId}`);
    sendToSimple({ type: 'keypress', key, windowId });
});

// IPC from renderer: action (tagged with windowId)
ipcMain.on('action', (event, name) => {
    const windowId = webContentsToWindowId.get(event.sender.id) || 'main';
    sendToSimple({ type: 'action', name, windowId });
});

// IPC from renderer: quit
ipcMain.on('quit', () => {
    sendToSimple({ type: 'quit' });
    if (simpleProcess) {
        simpleProcess.kill();
        simpleProcess = null;
    }
    app.quit();
});

// IPC from renderer: mouse / scroll / focus / input — for Canvas2D-rendered apps
// where the Simple program owns hit-testing, focus, and form state.
ipcMain.on('mouse', (event, payload) => {
    const kind = (payload && payload.kind) || 'move';
    if (kind !== 'move') debugLog(`mouse kind=${kind} button=${(payload && payload.button) || ''} x=${(payload && payload.x) || 0} y=${(payload && payload.y) || 0}`);
    sendToSimple({
        type: 'mouse',
        x: String((payload && payload.x) || 0),
        y: String((payload && payload.y) || 0),
        button: (payload && payload.button) || '',
        kind: kind
    });
});

ipcMain.on('scroll', (event, payload) => {
    sendToSimple({
        type: 'scroll',
        x: String((payload && payload.x) || 0),
        y: String((payload && payload.y) || 0),
        dx: String((payload && payload.dx) || 0),
        dy: String((payload && payload.dy) || 0)
    });
});

ipcMain.on('focusEvent', (event, payload) => {
    sendToSimple({
        type: 'focus',
        targetId: (payload && payload.targetId) || '',
        kind: (payload && payload.kind) || 'focus'
    });
});

ipcMain.on('inputChange', (event, payload) => {
    sendToSimple({
        type: 'input',
        targetId: (payload && payload.targetId) || '',
        value: (payload && payload.value) || ''
    });
});

ipcMain.handle('spawn-native-window', async (event, payload) => {
    return spawnNativeWindow(payload || {});
});

ipcMain.handle('close-native-window', async (event, payload) => {
    return closeNativeWindow(payload && payload.windowId);
});

ipcMain.handle('focus-native-window', async (event, payload) => {
    return focusNativeWindow(payload && payload.windowId);
});

ipcMain.handle('minimize-native-window', async (event, payload) => {
    return minimizeNativeWindow(payload && payload.windowId);
});

ipcMain.handle('restore-native-window', async (event, payload) => {
    return restoreNativeWindow(payload && payload.windowId);
});

ipcMain.handle('move-native-window', async (event, payload) => {
    return moveNativeWindow(
        payload && payload.windowId,
        payload && payload.x,
        payload && payload.y
    );
});

ipcMain.handle('resize-native-window', async (event, payload) => {
    return resizeNativeWindow(
        payload && payload.windowId,
        payload && payload.width,
        payload && payload.height
    );
});

ipcMain.handle('maximize-native-window', async (event, payload) => {
    return maximizeNativeWindow(payload && payload.windowId);
});

ipcMain.handle('unmaximize-native-window', async (event, payload) => {
    return unmaximizeNativeWindow(payload && payload.windowId);
});

ipcMain.handle('set-native-window-title', async (event, payload) => {
    return setNativeWindowTitle(
        payload && payload.windowId,
        payload && payload.title
    );
});

app.on('window-all-closed', () => {
    debugLog('window-all-closed');
    sendToSimple({ type: 'quit' });
    if (simpleProcess) {
        simpleProcess.kill();
        simpleProcess = null;
    }
    app.quit();
});

app.on('before-quit', () => {
    debugLog('before-quit');
});

app.on('quit', () => {
    debugLog('quit');
});
