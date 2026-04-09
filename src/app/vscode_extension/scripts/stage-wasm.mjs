import { copyFileSync, existsSync, mkdirSync } from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';

const scriptDir = path.dirname(fileURLToPath(import.meta.url));
const extensionRoot = path.resolve(scriptDir, '..');
const wasmDir = path.join(extensionRoot, 'wasm');

mkdirSync(wasmDir, { recursive: true });

const defaultBuildDir = process.env.SIMPLE_VSCODE_WASM_BUILD_DIR?.trim() || '';

const artifacts = [
    {
        envKey: 'SIMPLE_VSCODE_LSP_WASM_SOURCE',
        buildName: 'simple-lsp.wasm',
        targetName: 'simple-lsp.wasm',
    },
    {
        envKey: 'SIMPLE_VSCODE_MATH_WASM_SOURCE',
        buildName: 'math-core.wasm',
        targetName: 'math-core.wasm',
    },
];

let copiedCount = 0;

for (const artifact of artifacts) {
    const explicitSource = process.env[artifact.envKey]?.trim() || '';
    const inferredSource = defaultBuildDir ? path.join(defaultBuildDir, artifact.buildName) : '';
    const sourcePath = explicitSource || inferredSource;

    if (!sourcePath) {
        console.log(`[stage:wasm] ${artifact.targetName}: skipped (no ${artifact.envKey} or SIMPLE_VSCODE_WASM_BUILD_DIR)`);
        continue;
    }

    if (!existsSync(sourcePath)) {
        console.warn(`[stage:wasm] ${artifact.targetName}: source not found at ${sourcePath}`);
        continue;
    }

    const targetPath = path.join(wasmDir, artifact.targetName);
    copyFileSync(sourcePath, targetPath);
    copiedCount += 1;
    console.log(`[stage:wasm] copied ${artifact.targetName} <- ${sourcePath}`);
}

if (copiedCount === 0) {
    console.log('[stage:wasm] no WASM artifacts staged');
}
