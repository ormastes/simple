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

let mainWindow = null;
let simpleProcess = null;
let lineBuffer = '';
const debugLogPath = '/tmp/simple-ui-captures/electron-shell-debug.log';
const projectRoot = path.resolve(__dirname, '..', '..');

function debugLog(message) {
    const line = `[${new Date().toISOString()}] ${message}\n`;
    try {
        fs.appendFileSync(debugLogPath, line);
    } catch (err) {
        // Best-effort logging only.
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

// Collect non-flag arguments as the entry file and its args
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
        debugLog('no entry args provided');
        console.error('Usage: electron . <entry.spl> [args...]');
        console.error('  --bin <path>   Path to Simple binary (or set SIMPLE_BIN)');
        app.quit();
        return;
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
            SIMPLE_HOME: projectRoot
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
    mainWindow = new BrowserWindow({
        width: 1280,
        height: 720,
        webPreferences: {
            nodeIntegration: false,
            contextIsolation: true,
            preload: path.join(__dirname, 'preload.js')
        },
        title: 'Simple UI'
    });
    debugLog('browser window created');

    mainWindow.loadFile(path.join(__dirname, 'index.html'));
    debugLog('loadFile(index.html) requested');

    mainWindow.webContents.on('did-finish-load', () => {
        debugLog('window did-finish-load');
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

// IPC from renderer: keypress
ipcMain.on('keypress', (event, key) => {
    sendToSimple({ type: 'keypress', key });
});

// IPC from renderer: action
ipcMain.on('action', (event, name) => {
    sendToSimple({ type: 'action', name });
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
