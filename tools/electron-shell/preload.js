// Preload script for Simple UI Electron shell
//
// Exposes a safe bridge (window.simpleUI) between the renderer
// and the main process via contextBridge.

const { contextBridge, ipcRenderer } = require('electron');
const path = require('path');
const { pathToFileURL } = require('url');
const fs = require('fs');

const repoRoot = path.resolve(__dirname, '..', '..');

function readTextIfExists(filePath) {
    try {
        if (!filePath || !fs.existsSync(filePath)) return '';
        return fs.readFileSync(filePath, 'utf8');
    } catch {
        return '';
    }
}

function resolveRepoPath(rawPath) {
    if (!rawPath) return '';
    return path.isAbsolute(rawPath) ? rawPath : path.join(repoRoot, rawPath);
}

function rootValue(sdn, key) {
    const pattern = new RegExp(`^${key}:\\s*(.+)$`, 'm');
    const match = String(sdn || '').match(pattern);
    return match ? match[1].trim() : '';
}

function sectionValue(sdn, section, key) {
    const lines = String(sdn || '').split(/\r?\n/);
    let inSection = false;
    for (const line of lines) {
        if (!line.trim() || line.trim().startsWith('#')) continue;
        if (!line.startsWith(' ') && line.endsWith(':')) {
            inSection = line.slice(0, -1).trim() === section;
            continue;
        }
        if (inSection) {
            const trimmed = line.trim();
            const prefix = `${key}:`;
            if (trimmed.startsWith(prefix)) return trimmed.slice(prefix.length).trim();
        }
    }
    return '';
}

function sectionList(sdn, section) {
    const lines = String(sdn || '').split(/\r?\n/);
    const values = [];
    let inSection = false;
    for (const line of lines) {
        if (!line.trim() || line.trim().startsWith('#')) continue;
        if (!line.startsWith(' ') && line.endsWith(':')) {
            inSection = line.slice(0, -1).trim() === section;
            continue;
        }
        if (inSection) {
            const trimmed = line.trim();
            if (trimmed.startsWith('- ')) values.push(trimmed.slice(2).trim());
        }
    }
    return values;
}

function loadWidgetCss(widgets, themeDir, familyDir) {
    const chunks = [];
    for (const widget of widgets) {
        const themePath = resolveRepoPath(path.join(themeDir || '', `${widget}.css`));
        const familyPath = resolveRepoPath(path.join(familyDir || '', `${widget}.css`));
        const defaultPath = resolveRepoPath(path.join(familyDir || '', 'defaults.css'));
        chunks.push(readTextIfExists(themePath) || readTextIfExists(familyPath) || readTextIfExists(defaultPath));
    }
    return chunks.filter(Boolean).join('\n');
}

function loadHostThemePackage() {
    const registryPath = path.join(repoRoot, 'config', 'themes', 'theme.sdn');
    const registry = readTextIfExists(registryPath);
    const themeId = rootValue(registry, 'default_theme') || 'aetheric_dark';
    const themePath = resolveRepoPath(sectionValue(registry, 'themes', themeId) || `config/themes/${themeId}/theme.sdn`);
    const themeSdn = readTextIfExists(themePath);
    const familyId = rootValue(themeSdn, 'family');
    const familyPath = resolveRepoPath(sectionValue(registry, 'families', familyId) || `config/themes/families/${familyId}/theme.sdn`);
    const familySdn = readTextIfExists(familyPath);
    const shapeCssPath = rootValue(familySdn, 'shape_css');
    const baseCssPath = rootValue(themeSdn, 'base_css');
    const familyWidgetDir = rootValue(familySdn, 'widget_css_dir');
    const themeWidgetDir = rootValue(themeSdn, 'widget_css_dir');
    const widgets = sectionList(registry, 'required_widgets');
    const css = [
        readTextIfExists(resolveRepoPath(shapeCssPath)),
        loadWidgetCss(widgets, '', familyWidgetDir),
        readTextIfExists(resolveRepoPath(baseCssPath)),
        loadWidgetCss(widgets, themeWidgetDir, '')
    ].filter(Boolean).join('\n');
    return {
        id: themeId,
        displayName: rootValue(themeSdn, 'display_name') || themeId,
        css
    };
}

const hostTheme = loadHostThemePackage();

contextBridge.exposeInMainWorld('simpleUI', {
    rendererModuleUrl: pathToFileURL(path.join(repoRoot, 'src', 'app', 'ui.web', 'retained_renderer.js')).href,
    hostThemeId: hostTheme.id,
    hostThemeDisplayName: hostTheme.displayName,
    hostThemeCss: hostTheme.css,
    nativeHostWindows:
        process.env.SIMPLE_ELECTRON_HOST_WINDOW_MODE === 'native' ||
        process.env.SIMPLE_ELECTRON_NATIVE_SMOKE === '1',
    platform: process.platform,

    // Receive HTML render updates from the Simple process (desktop chrome).
    onRender(callback) {
        ipcRenderer.on('render', (event, html) => {
            callback(html);
        });
    },

    // Receive legacy window-manager messages forwarded from main.js. These
    // are adapted by wm.js receiveElectronMessage() so the shell no longer
    // depends on the removed handleMessage() path.
    //
    // Message shape:
    //   { type: 'openWindow'  | 'closeWindow' | 'renderWindow'
    //           | 'moveWindow' | 'resizeWindow' | 'focusWindow'
    //           | 'minimizeWindow',
    //     windowId, title?, html?, x?, y?, width?, height? }
    onWmMessage(callback) {
        ipcRenderer.on('wm-message', (event, msg) => {
            callback(msg);
        });
    },

    onWmFrame(callback) {
        ipcRenderer.on('wm-frame', (event, frame) => {
            callback(frame);
        });
    },

    sendFrame(frame) {
        ipcRenderer.send('wm-frame-to-simple', frame || {});
    },

    notifyWmReady() {
        ipcRenderer.send('wm-ready');
    },

    onNativeWindowEvent(callback) {
        ipcRenderer.on('native-window-event', (event, msg) => {
            callback(msg);
        });
    },

    // Send a keypress event to the Simple process
    sendKeypress(key) {
        ipcRenderer.send('keypress', key);
    },

    // Send a named action to the Simple process
    sendAction(name) {
        ipcRenderer.send('action', name);
    },

    // Send quit signal to the Simple process
    sendQuit() {
        ipcRenderer.send('quit');
    },

    spawnNativeWindow(windowId, url, width, height, title) {
        return ipcRenderer.invoke('spawn-native-window', { windowId, url, width, height, title });
    },

    closeNativeWindow(windowId) {
        return ipcRenderer.invoke('close-native-window', { windowId });
    },

    focusNativeWindow(windowId) {
        return ipcRenderer.invoke('focus-native-window', { windowId });
    },

    minimizeNativeWindow(windowId) {
        return ipcRenderer.invoke('minimize-native-window', { windowId });
    },

    restoreNativeWindow(windowId) {
        return ipcRenderer.invoke('restore-native-window', { windowId });
    },

    moveNativeWindow(windowId, x, y) {
        return ipcRenderer.invoke('move-native-window', { windowId, x, y });
    },

    resizeNativeWindow(windowId, width, height) {
        return ipcRenderer.invoke('resize-native-window', { windowId, width, height });
    },

    maximizeNativeWindow(windowId) {
        return ipcRenderer.invoke('maximize-native-window', { windowId });
    },

    unmaximizeNativeWindow(windowId) {
        return ipcRenderer.invoke('unmaximize-native-window', { windowId });
    },

    setNativeWindowTitle(windowId, title) {
        return ipcRenderer.invoke('set-native-window-title', { windowId, title });
    },

    // ============================================================================
    // Canvas2D paint pipeline — used when the Simple program renders via the
    // Blink-style engine at src/lib/blink/ instead of emitting HTML.
    // ============================================================================

    // Receive a Canvas2D ops payload from the Simple process.
    // payload = { ops: [{op:..., ...}, ...], width, height }
    onPaintCanvas(callback) {
        ipcRenderer.on('paint-canvas', (event, payload) => {
            callback(payload);
        });
    },

    // Forward a mouse event to the Simple process.
    // payload = { x, y, button: 'left'|'right'|'middle'|'', kind: 'down'|'up'|'move' }
    sendMouse(payload) {
        ipcRenderer.send('mouse', payload || {});
    },

    // Forward a scroll/wheel event to the Simple process.
    // payload = { x, y, dx, dy }
    sendScroll(payload) {
        ipcRenderer.send('scroll', payload || {});
    },

    // Forward a focus/blur event to the Simple process.
    // payload = { targetId, kind: 'focus'|'blur' }
    sendFocus(payload) {
        ipcRenderer.send('focusEvent', payload || {});
    },

    // Forward an input value change to the Simple process.
    // payload = { targetId, value }
    sendInput(payload) {
        ipcRenderer.send('inputChange', payload || {});
    }
});
