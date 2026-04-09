import { copyFileSync, existsSync, mkdirSync, readFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';

const scriptDir = path.dirname(fileURLToPath(import.meta.url));
const extensionRoot = path.resolve(scriptDir, '..');
const wasmDir = path.join(extensionRoot, 'wasm');
const mathCoreCrateDir = path.join(extensionRoot, 'math_core_rs');
const mathCoreCargoToml = path.join(mathCoreCrateDir, 'Cargo.toml');
const buildMathCoreRs = process.argv.includes('--build-math-core-rs');

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
        buildFromRust: true,
    },
];

let copiedCount = 0;

for (const artifact of artifacts) {
    const explicitSource = process.env[artifact.envKey]?.trim() || '';
    const inferredSource = defaultBuildDir ? path.join(defaultBuildDir, artifact.buildName) : '';
    let sourcePath = explicitSource || inferredSource;

    if (!sourcePath && artifact.buildFromRust && buildMathCoreRs) {
        sourcePath = buildMathCoreWasmArtifact();
    }

    if (!sourcePath) {
        const fallbackNote = artifact.buildFromRust
            ? `no ${artifact.envKey}, SIMPLE_VSCODE_WASM_BUILD_DIR, or --build-math-core-rs`
            : `no ${artifact.envKey} or SIMPLE_VSCODE_WASM_BUILD_DIR`;
        console.log(`[stage:wasm] ${artifact.targetName}: skipped (${fallbackNote})`);
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

function buildMathCoreWasmArtifact() {
    if (!existsSync(mathCoreCargoToml)) {
        throw new Error(`[stage:wasm] math-core crate not found at ${mathCoreCargoToml}`);
    }

    const cargo = spawnSync(
        'cargo',
        [
            'build',
            '--manifest-path',
            mathCoreCargoToml,
            '--target',
            'wasm32-unknown-unknown',
            '--release',
            '--target-dir',
            path.join(mathCoreCrateDir, 'target'),
        ],
        {
            cwd: extensionRoot,
            encoding: 'utf8',
            stdio: ['ignore', 'pipe', 'pipe'],
        }
    );

    if (cargo.status !== 0) {
        const details = [cargo.stdout, cargo.stderr].filter(Boolean).join('\n').trim();
        throw new Error(
            `[stage:wasm] failed to build math-core wasm crate via cargo.\n${details || 'cargo build returned a non-zero exit code.'}`
        );
    }

    const packageName = readCargoPackageName(mathCoreCargoToml);
    const artifactStem = packageName.replace(/-/g, '_');
    const builtArtifact = path.join(
        mathCoreCrateDir,
        'target',
        'wasm32-unknown-unknown',
        'release',
        `${artifactStem}.wasm`
    );

    if (!existsSync(builtArtifact)) {
        throw new Error(
            `[stage:wasm] cargo build succeeded, but expected artifact was not found at ${builtArtifact}`
        );
    }

    console.log(`[stage:wasm] built math-core.wasm <- ${builtArtifact}`);
    return builtArtifact;
}

function readCargoPackageName(cargoTomlPath) {
    const cargoToml = readFileSync(cargoTomlPath, 'utf8');
    const match = cargoToml.match(/^\s*name\s*=\s*"([^"]+)"/m);
    if (!match) {
        throw new Error(`[stage:wasm] could not determine package name from ${cargoTomlPath}`);
    }
    return match[1];
}
