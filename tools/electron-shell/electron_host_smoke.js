#!/usr/bin/env node

const { spawn } = require('child_process');
const path = require('path');
const fs = require('fs');

const shellDir = __dirname;

function skip(reason) {
    console.log(`SKIP: ${reason}`);
    process.exit(0);
}

if (process.env.SIMPLE_ELECTRON_SMOKE !== '1') {
    skip('set SIMPLE_ELECTRON_SMOKE=1 to run the opt-in Electron host smoke');
}

if (process.platform === 'linux' && !process.env.DISPLAY && !process.env.WAYLAND_DISPLAY) {
    skip('no DISPLAY or WAYLAND_DISPLAY available for Electron');
}

let electronPath = '';
try {
    electronPath = require('electron');
} catch (err) {
    skip('Electron package is not installed; run npm --prefix tools/electron-shell ci first');
}

if (typeof electronPath !== 'string' || !electronPath) {
    skip('Electron executable could not be resolved');
}

if (!fs.existsSync(electronPath)) {
    skip(`Electron executable is missing at ${electronPath}`);
}

const child = spawn(electronPath, [shellDir, '--smoke-native-window'], {
    cwd: path.resolve(shellDir, '..', '..'),
    env: {
        ...process.env,
        SIMPLE_ELECTRON_NATIVE_SMOKE: '1'
    },
    stdio: ['ignore', 'pipe', 'pipe']
});

const timeout = setTimeout(() => {
    child.kill('SIGTERM');
    console.error('Electron native smoke timed out');
    process.exit(1);
}, Number(process.env.SIMPLE_ELECTRON_SMOKE_TIMEOUT_MS || 15000));

child.stdout.on('data', (data) => process.stdout.write(data));
child.stderr.on('data', (data) => process.stderr.write(data));

child.on('error', (err) => {
    clearTimeout(timeout);
    console.error(`Electron native smoke failed to launch: ${err.message}`);
    process.exit(1);
});

child.on('exit', (code, signal) => {
    clearTimeout(timeout);
    if (signal) {
        console.error(`Electron native smoke exited by signal ${signal}`);
        process.exit(1);
    }
    process.exit(code == null ? 1 : code);
});
