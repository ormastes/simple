#!/usr/bin/env node

const fs = require('fs');
const path = require('path');
const vm = require('vm');

const projectRoot = path.resolve(__dirname, '..', '..');
const wmSource = fs.readFileSync(path.join(projectRoot, 'src', 'app', 'ui.web', 'wm.js'), 'utf8');

class FakeElement {
    constructor(id = '') {
        this.id = id;
        this.children = [];
        this.dataset = {};
        this.style = {};
        this.className = '';
        this.textContent = '';
        this.innerHTML = '';
        this.parentNode = null;
        this.classList = {
            add: () => {},
            remove: () => {}
        };
    }

    appendChild(child) {
        child.parentNode = this;
        this.children.push(child);
        return child;
    }

    remove() {
        if (!this.parentNode) return;
        this.parentNode.children = this.parentNode.children.filter((child) => child !== this);
        this.parentNode = null;
    }

    addEventListener() {}
}

function createHarness(options = {}) {
    const desktop = new FakeElement('wm-desktop');
    const taskbar = new FakeElement('wm-taskbar');
    const sentFrames = [];
    let spawnCount = 0;

    const context = {
        console,
        setTimeout,
        clearTimeout,
        setInterval,
        clearInterval,
        location: { protocol: 'file:', host: '' },
        document: {
            getElementById(id) {
                if (id === 'wm-desktop') return desktop;
                if (id === 'wm-taskbar') return taskbar;
                return new FakeElement(id);
            },
            createElement(tag) {
                return new FakeElement(tag);
            },
            addEventListener() {},
            body: new FakeElement('body')
        },
        window: {
            simpleUI: {
                sendFrame(frame) {
                    sentFrames.push(frame);
                },
                notifyWmReady() {},
                spawnNativeWindow() {
                    spawnCount += 1;
                    return Promise.resolve(true);
                }
            }
        }
    };
    context.globalThis = context;

    const script = new vm.Script(`${wmSource}\nSimpleWindowManager;`, {
        filename: 'wm.js'
    });
    const SimpleWindowManager = script.runInNewContext(context);
    const manager = new SimpleWindowManager({
        transport: 'electron-ipc',
        nativeHostWindows: !!options.nativeHostWindows
    });
    return {
        manager,
        desktop,
        sentFrames,
        get spawnCount() {
            return spawnCount;
        }
    };
}

async function main() {
    const embedded = createHarness();
    await embedded.manager._handleHostWindowCommand({
        action: 'spawn_native_window',
        window_id: 'host-window-1',
        app_id: 'examples/hello_taskbar',
        title: 'Hello',
        url: '/wm/native_window?app_id=examples%2Fhello_taskbar',
        width: 500,
        height: 300
    });

    if (embedded.spawnCount !== 0) {
        throw new Error('embedded mode called spawnNativeWindow');
    }
    if (embedded.desktop.children.length !== 1) {
        throw new Error(`embedded mode created ${embedded.desktop.children.length} WM windows`);
    }
    const embeddedBody = embedded.desktop.children[0].children[1];
    if (!embeddedBody || embeddedBody.innerHTML.includes('<iframe')) {
        throw new Error('embedded mode rendered relative native-window URL as an iframe');
    }
    if (!embeddedBody.innerHTML.includes('examples/hello_taskbar')) {
        throw new Error('embedded mode fallback did not render app identity');
    }
    if (!embedded.sentFrames.some((frame) =>
        frame.t === 'window_cmd' &&
        frame.payload &&
        frame.payload.cmd_type === 'focus' &&
        frame.payload.source === 'native_event'
    )) {
        throw new Error('embedded mode did not send native_event focus sync');
    }

    const native = createHarness({ nativeHostWindows: true });
    await native.manager._handleHostWindowCommand({
        action: 'spawn_native_window',
        window_id: 'host-window-native',
        title: 'Native',
        width: 400,
        height: 250
    });
    if (native.spawnCount !== 1) {
        throw new Error(`native mode spawn count was ${native.spawnCount}`);
    }
    if (native.desktop.children.length !== 0) {
        throw new Error('native mode unexpectedly created embedded WM windows');
    }

    console.log('Electron embedded host-window smoke passed');
}

main().catch((err) => {
    console.error(`Electron embedded host-window smoke failed: ${err.stack || err.message || err}`);
    process.exit(1);
});
