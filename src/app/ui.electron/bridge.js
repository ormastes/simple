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
            const rendered = win.webContents.executeJavaScript(renderEnvelopeScript(msg));
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

function electronAppEntryPath() {
    return path.resolve(__dirname, '../../../src/app/ui.electron/app.spl');
}

function startSimpleProcess(simpleBin, entry) {
    if (!simpleBin || !entry) {
        return null;
    }
    const child = spawn(simpleBin, ['run', electronAppEntryPath(), entry], {
        cwd: path.resolve(__dirname, '../../..'),
        stdio: ['pipe', 'pipe', 'pipe']
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
    handleSimpleMessageLine,
    parseCliArgs,
    renderEnvelopeMetadata,
    renderEnvelopeScript
};
