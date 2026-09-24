import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import test from 'node:test';
import {
    detectVscodeExecutable,
    prepareVscodeTestBundle,
    removeIncompleteVscodeBundles,
} from './vscode-test-bundle.mjs';

function fixtureRoot() {
    return fs.mkdtempSync(path.join(os.tmpdir(), 'simple-vscode-bundle-'));
}

function writeExecutable(bundlePath, platform = process.platform, nested = false, currentMacLayout = false) {
    const root = nested ? path.join(bundlePath, 'archive-root') : bundlePath;
    const relative = platform === 'darwin'
        ? `Visual Studio Code.app/Contents/MacOS/${currentMacLayout ? 'Code' : 'Electron'}`
        : platform === 'win32' ? 'Code.exe' : 'code';
    const executable = path.join(root, relative);
    fs.mkdirSync(path.dirname(executable), { recursive: true });
    fs.writeFileSync(executable, 'fixture');
    fs.chmodSync(executable, 0o755);
    return executable;
}

test('detects direct and one-directory archive layouts', () => {
    const root = fixtureRoot();
    try {
        const direct = path.join(root, 'direct');
        const nested = path.join(root, 'nested');
        fs.mkdirSync(direct);
        fs.mkdirSync(nested);
        const directExecutable = writeExecutable(direct);
        const nestedExecutable = writeExecutable(nested, process.platform, true);
        assert.equal(detectVscodeExecutable(direct), directExecutable);
        assert.equal(detectVscodeExecutable(nested), nestedExecutable);
    } finally {
        fs.rmSync(root, { recursive: true, force: true });
    }
});

test('detects the current macOS Code executable and the legacy Electron executable', () => {
    const root = fixtureRoot();
    try {
        const current = path.join(root, 'current');
        const legacy = path.join(root, 'legacy');
        fs.mkdirSync(current);
        fs.mkdirSync(legacy);
        const currentExecutable = writeExecutable(current, 'darwin', false, true);
        const legacyExecutable = writeExecutable(legacy, 'darwin');
        assert.equal(detectVscodeExecutable(current, 'darwin'), currentExecutable);
        assert.equal(detectVscodeExecutable(legacy, 'darwin'), legacyExecutable);
    } finally {
        fs.rmSync(root, { recursive: true, force: true });
    }
});

test('removes cache entries whose completion marker lacks an executable', () => {
    const root = fixtureRoot();
    try {
        const cache = path.join(root, 'cache');
        const broken = path.join(cache, 'vscode-darwin-arm64-1.0.0');
        fs.mkdirSync(broken, { recursive: true });
        fs.writeFileSync(path.join(broken, 'is-complete'), '');
        assert.deepEqual(removeIncompleteVscodeBundles(cache), [broken]);
        assert.equal(fs.existsSync(broken), false);
    } finally {
        fs.rmSync(root, { recursive: true, force: true });
    }
});

test('publishes a validated download atomically under centralized user storage', async () => {
    const root = fixtureRoot();
    try {
        const result = await prepareVscodeTestBundle({
            userStorageRoot: root,
            download: async ({ cachePath }) => {
                const bundle = path.join(cachePath, 'vscode-fixture-1.0.0');
                fs.mkdirSync(bundle, { recursive: true });
                return writeExecutable(bundle);
            },
        });
        assert.equal(result.reused, false);
        assert.equal(path.relative(root, result.bundlePath).startsWith('..'), false);
        assert.equal(fs.existsSync(result.executablePath), true);
        assert.deepEqual(fs.readdirSync(result.cachePath).filter((name) => name.startsWith('.staging-')), []);
    } finally {
        fs.rmSync(root, { recursive: true, force: true });
    }
});

test('preserves a valid bundle published concurrently', async () => {
    const root = fixtureRoot();
    try {
        const result = await prepareVscodeTestBundle({
            userStorageRoot: root,
            download: async ({ cachePath }) => {
                const staged = path.join(cachePath, 'vscode-fixture-1.0.0');
                fs.mkdirSync(staged, { recursive: true });
                writeExecutable(staged);
                const finalBundle = path.join(root, 'cache', 'vscode-test', 'bundles', path.basename(staged));
                fs.mkdirSync(finalBundle, { recursive: true });
                const winner = writeExecutable(finalBundle);
                fs.writeFileSync(winner, 'winner');
                return detectVscodeExecutable(staged);
            },
        });
        assert.equal(result.reused, true);
        assert.equal(fs.readFileSync(result.executablePath, 'utf8'), 'winner');
    } finally {
        fs.rmSync(root, { recursive: true, force: true });
    }
});

test('fails closed and removes staging when download lacks an executable', async () => {
    const root = fixtureRoot();
    try {
        await assert.rejects(prepareVscodeTestBundle({
            userStorageRoot: root,
            download: async ({ cachePath }) => {
                const bundle = path.join(cachePath, 'vscode-fixture-broken');
                fs.mkdirSync(bundle, { recursive: true });
                fs.writeFileSync(path.join(bundle, 'is-complete'), '');
                return path.join(bundle, 'missing-electron');
            },
        }), /incomplete/);
        const cache = path.join(root, 'cache', 'vscode-test', 'bundles');
        assert.deepEqual(fs.readdirSync(cache), []);
    } finally {
        fs.rmSync(root, { recursive: true, force: true });
    }
});
