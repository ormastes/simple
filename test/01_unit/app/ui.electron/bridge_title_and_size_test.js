const assert = require('assert');
const fs = require('fs');
const path = require('path');

const bridge = require('../../../../src/app/ui.electron/bridge.js');
const bridgeSrc = fs.readFileSync(
    path.join(__dirname, '../../../../src/app/ui.electron/bridge.js'),
    'utf8'
);
const electronAppSrc = fs.readFileSync(
    path.join(__dirname, '../../../../src/app/ui.electron/app.spl'),
    'utf8'
);

// 1. formatElectronWindowTitle enforces "[Chrome Base / Electron]"
assert.strictEqual(
    bridge.formatElectronWindowTitle(''),
    'Simple Browser — [Chrome Base / Electron]'
);
assert.strictEqual(
    bridge.formatElectronWindowTitle('   '),
    'Simple Browser — [Chrome Base / Electron]'
);
assert.strictEqual(
    bridge.formatElectronWindowTitle('Simple UI'),
    'Simple UI — [Chrome Base / Electron]'
);
assert.strictEqual(
    bridge.formatElectronWindowTitle('Kitchen Sink Demo'),
    'Kitchen Sink Demo — [Chrome Base / Electron]'
);
assert.strictEqual(
    bridge.formatElectronWindowTitle('Custom — [Chrome Base / Electron]'),
    'Custom — [Chrome Base / Electron]'
);

// 2. Default 960x640 size, content-area sizing, visible title bar, unconditional title lock, capture & quit
assert(bridgeSrc.includes('Number(process.env.SIMPLE_ELECTRON_WIDTH) || 960'));
assert(bridgeSrc.includes('Number(process.env.SIMPLE_ELECTRON_HEIGHT) || 640'));
assert(bridgeSrc.includes('useContentSize: true'));
assert(bridgeSrc.includes('show: true'));
assert(bridgeSrc.includes("SIMPLE_ELECTRON_HIDE_TITLEBAR === '1'"));
assert(bridgeSrc.includes('formatElectronWindowTitle'));
assert(bridgeSrc.includes("mainWindow.on('page-title-updated'"));
assert(bridgeSrc.includes("did-finish-load"));
assert(bridgeSrc.includes('SIMPLE_ELECTRON_CAPTURE_AND_QUIT_PATH'));
assert(bridgeSrc.includes('capturePage()'));

// 3. handleSimpleMessageLine renders cleanly on mock window with show/focus hooks
let shown = false;
let focused = false;
const mockWin = {
    show() { shown = true; },
    focus() { focused = true; },
    webContents: {
        executeJavaScript() { return Promise.resolve(); }
    }
};
const res = bridge.handleSimpleMessageLine(
    JSON.stringify({ type: 'render', html: '<div id="root"></div>', css: '', target: 'electron' }),
    mockWin
);
assert.strictEqual(res.handled, true);
assert.strictEqual(res.kind, 'render');
assert.strictEqual(shown, true);
assert.strictEqual(focused, true);

// 4. ui.electron/app.spl tracks viewport dimensions defaulting to 960x640 and updates on Resize
assert(electronAppSrc.includes('var vp_w: i32 = 960'));
assert(electronAppSrc.includes('var vp_h: i32 = 640'));
assert(electronAppSrc.includes('UIEvent.Resize(w, h):'));
assert(electronAppSrc.includes('electron_render_ipc_json(state, width, height)'));

console.log('bridge_title_and_size_test: PASS');
