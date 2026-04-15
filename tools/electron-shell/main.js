// Electron main process for Simple Language UI
//
// Spawns a Simple binary as a subprocess and bridges JSON IPC
// between the Simple process (stdin/stdout) and the Electron renderer.
//
// Usage:
//   electron . <entry.spl>
//   SIMPLE_BIN=/path/to/simple electron . <entry.spl>

const { app, BrowserWindow, ipcMain, dialog, Notification } = require('electron');
const { spawn } = require('child_process');
const path = require('path');
const fs = require('fs');
const os = require('os');

let mainWindow = null;
let simpleProcess = null;
let lineBuffer = '';
// childWindows/webContentsToWindowId were used by the old openWindow
// handler that spawned separate BrowserWindow instances. The WM now
// runs in the main renderer (wm.js) so there are no child BrowserWindows.
const webContentsToWindowId = new Map();  // webContents.id → windowId (main only)
const debugLogPath = '/tmp/simple-ui-captures/electron-shell-debug.log';
const dumpHtmlPath = process.env.SIMPLE_UI_DUMP_HTML_PATH || '';
const projectRoot = path.resolve(__dirname, '..', '..');

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

// Resolve Simple binary path: CLI arg --bin, env SIMPLE_BIN, or default
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
    return path.join(__dirname, '..', '..', 'bin', 'simple');
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

// Handle a single JSON line from the Simple subprocess stdout
function handleSimpleMessage(line) {
    if (!line.trim()) return;
    try {
        const msg = JSON.parse(line);
        debugLog(`ipc message type=${msg.type || 'unknown'}`);
        switch (msg.type) {
            case 'render':
                if (mainWindow) {
                    dumpRenderedHtml(msg.html || '');
                    mainWindow.webContents.send('render', msg.html);
                }
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

    spawnSimpleProcess();
});

// IPC from renderer: keypress (tagged with windowId)
ipcMain.on('keypress', (event, key) => {
    const windowId = webContentsToWindowId.get(event.sender.id) || 'main';
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
