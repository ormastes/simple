import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { randomUUID } from 'node:crypto';

const CACHE_DIRECTORY = path.join('cache', 'vscode-test', 'bundles');
const DOWNLOAD_DIRECTORY_PREFIX = 'vscode-';

function executableCandidates(bundlePath, platform = process.platform) {
    const roots = [bundlePath];
    for (const entry of fs.readdirSync(bundlePath, { withFileTypes: true })) {
        if (entry.isDirectory() && !entry.name.endsWith('.app')) {
            roots.push(path.join(bundlePath, entry.name));
        }
    }

    const relativeCandidates = platform === 'darwin'
        ? [
            'Visual Studio Code.app/Contents/MacOS/Code',
            'Visual Studio Code.app/Contents/MacOS/Electron',
            'Visual Studio Code - Insiders.app/Contents/MacOS/Code - Insiders',
            'Visual Studio Code - Insiders.app/Contents/MacOS/Code',
            'Visual Studio Code - Insiders.app/Contents/MacOS/Electron',
        ]
        : platform === 'win32'
            ? ['Code.exe', 'Code - Insiders.exe']
            : ['code', 'code-insiders'];
    return roots.flatMap((root) => relativeCandidates.map((candidate) => path.join(root, candidate)));
}

function platformFamily(platform) {
    if (!platform) {
        return process.platform;
    }
    if (platform.startsWith('darwin')) {
        return 'darwin';
    }
    if (platform.startsWith('win32')) {
        return 'win32';
    }
    return 'linux';
}

export function detectVscodeExecutable(bundlePath, platform = process.platform) {
    if (!fs.existsSync(bundlePath) || !fs.statSync(bundlePath).isDirectory()) {
        return undefined;
    }
    for (const candidate of executableCandidates(bundlePath, platform)) {
        try {
            fs.accessSync(candidate, platform === 'win32' ? fs.constants.F_OK : fs.constants.X_OK);
            if (fs.statSync(candidate).isFile()) {
                return candidate;
            }
        } catch {
            // Try the next supported archive layout.
        }
    }
    return undefined;
}

function installedBundles(cachePath) {
    if (!fs.existsSync(cachePath)) {
        return [];
    }
    return fs.readdirSync(cachePath, { withFileTypes: true })
        .filter((entry) => entry.isDirectory() && entry.name.startsWith(DOWNLOAD_DIRECTORY_PREFIX))
        .map((entry) => path.join(cachePath, entry.name));
}

export function removeIncompleteVscodeBundles(cachePath, platform = process.platform) {
    const removed = [];
    for (const bundlePath of installedBundles(cachePath)) {
        if (!detectVscodeExecutable(bundlePath, platform)) {
            fs.rmSync(bundlePath, { recursive: true, force: true });
            removed.push(bundlePath);
        }
    }
    return removed;
}

function newestValidBundle(cachePath, platform) {
    return installedBundles(cachePath)
        .map((bundlePath) => ({ bundlePath, executablePath: detectVscodeExecutable(bundlePath, platform) }))
        .filter((entry) => entry.executablePath)
        .sort((left, right) => right.bundlePath.localeCompare(left.bundlePath))[0];
}

function containingBundle(executablePath, stagingPath) {
    let candidate = path.resolve(executablePath);
    const stagingRoot = path.resolve(stagingPath);
    while (path.dirname(candidate) !== stagingRoot && candidate !== stagingRoot) {
        candidate = path.dirname(candidate);
    }
    if (path.dirname(candidate) !== stagingRoot) {
        throw new Error(`Downloaded VS Code executable escaped staging cache: ${executablePath}`);
    }
    return candidate;
}

export async function prepareVscodeTestBundle({
    userStorageRoot,
    version = 'stable',
    platform,
    download,
}) {
    const cachePath = path.join(path.resolve(userStorageRoot), CACHE_DIRECTORY);
    const hostPlatform = platformFamily(platform);
    fs.mkdirSync(cachePath, { recursive: true });
    removeIncompleteVscodeBundles(cachePath, hostPlatform);

    const existing = newestValidBundle(cachePath, hostPlatform);
    if (existing) {
        return { ...existing, cachePath, reused: true };
    }

    const stagingPath = path.join(cachePath, `.staging-${randomUUID()}`);
    fs.mkdirSync(stagingPath, { recursive: true });
    try {
        const downloadedExecutable = await download({ version, platform, cachePath: stagingPath });
        const stagedBundle = containingBundle(downloadedExecutable, stagingPath);
        const executablePath = detectVscodeExecutable(stagedBundle, hostPlatform);
        if (!executablePath) {
            throw new Error(`Downloaded VS Code bundle is incomplete: no supported executable under ${stagedBundle}`);
        }

        const bundlePath = path.join(cachePath, path.basename(stagedBundle));
        const winningExecutable = detectVscodeExecutable(bundlePath, hostPlatform);
        if (winningExecutable) {
            return { bundlePath, executablePath: winningExecutable, cachePath, reused: true };
        }
        if (fs.existsSync(bundlePath)) {
            fs.rmSync(bundlePath, { recursive: true, force: true });
        }
        try {
            fs.renameSync(stagedBundle, bundlePath);
        } catch (error) {
            const concurrentExecutable = detectVscodeExecutable(bundlePath, hostPlatform);
            if (concurrentExecutable) {
                return { bundlePath, executablePath: concurrentExecutable, cachePath, reused: true };
            }
            throw error;
        }
        const publishedExecutable = detectVscodeExecutable(bundlePath, hostPlatform);
        if (!publishedExecutable) {
            fs.rmSync(bundlePath, { recursive: true, force: true });
            throw new Error(`Published VS Code bundle failed executable validation: ${bundlePath}`);
        }
        return { bundlePath, executablePath: publishedExecutable, cachePath, reused: false };
    } finally {
        fs.rmSync(stagingPath, { recursive: true, force: true });
    }
}
