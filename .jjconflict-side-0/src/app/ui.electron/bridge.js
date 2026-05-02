// Minimal Electron shell for Simple UI
//
// Launches a BrowserWindow and bridges IPC between the Simple process
// (stdin/stdout JSON) and the Electron renderer (BrowserWindow).
//
// Usage: electron bridge.js [--port PORT]

const { app, BrowserWindow, ipcMain, dialog, Notification } = require('electron');
const { spawn } = require('child_process');
const path = require('path');

let mainWindow = null;
let simpleProcess = null;

// Parse command line args
const args = process.argv.slice(2);
let port = 3000;
for (let i = 0; i < args.length; i++) {
    if (args[i] === '--port' && i + 1 < args.length) {
        port = parseInt(args[i + 1]);
        i++;
    }
}

app.whenReady().then(() => {
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

    // Load the web UI from the Simple server
    mainWindow.loadURL(`http://localhost:${port}`);

    // Forward window events to Simple process
    mainWindow.on('resize', () => {
        const [width, height] = mainWindow.getContentSize();
        sendToSimple({ type: 'resize', width, height });
    });

    mainWindow.on('closed', () => {
        mainWindow = null;
        sendToSimple({ type: 'quit' });
    });
});

// IPC handlers for native features
ipcMain.handle('show-dialog', async (event, options) => {
    const result = await dialog.showMessageBox(mainWindow, options);
    return result;
});

ipcMain.handle('show-open-dialog', async (event, options) => {
    const result = await dialog.showOpenDialog(mainWindow, options);
    return result;
});

ipcMain.handle('show-save-dialog', async (event, options) => {
    const result = await dialog.showSaveDialog(mainWindow, options);
    return result;
});

ipcMain.handle('show-notification', async (event, { title, body }) => {
    new Notification({ title, body }).show();
});

// Stdin/stdout IPC with Simple process
function sendToSimple(msg) {
    if (simpleProcess && simpleProcess.stdin.writable) {
        simpleProcess.stdin.write(JSON.stringify(msg) + '\n');
    }
}

// Handle messages from Simple process (stdout)
function handleSimpleMessage(line) {
    try {
        const msg = JSON.parse(line);
        if (msg.type === 'render' && mainWindow) {
            mainWindow.webContents.send('render', msg.html);
        } else if (msg.type === 'dialog') {
            dialog.showMessageBox(mainWindow, {
                type: msg.dialogType || 'info',
                title: msg.title || '',
                message: msg.message || ''
            });
        } else if (msg.type === 'notification') {
            new Notification({ title: msg.title, body: msg.body }).show();
        } else if (msg.type === 'windowControl' || msg.type === 'window_control') {
            switch (msg.action) {
                case 'minimize': mainWindow.minimize(); break;
                case 'maximize': mainWindow.isMaximized() ? mainWindow.unmaximize() : mainWindow.maximize(); break;
                case 'close': mainWindow.close(); break;
            }
        }
    } catch (e) {
        // Ignore non-JSON lines
    }
}

app.on('window-all-closed', () => {
    app.quit();
});
