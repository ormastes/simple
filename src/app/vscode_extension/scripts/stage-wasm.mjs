import { copyFileSync, existsSync, mkdirSync, readFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';

const scriptDir = path.dirname(fileURLToPath(import.meta.url));
const extensionRoot = path.resolve(scriptDir, '..');
const repoRoot = path.resolve(extensionRoot, '..', '..', '..');
const wasmDir = path.join(extensionRoot, 'wasm');
const wasmBuildDir = path.join(extensionRoot, '.wasm-build');
const mathCoreCrateDir = path.join(extensionRoot, 'math_core_rs');
const mathCoreCargoToml = path.join(mathCoreCrateDir, 'Cargo.toml');
const simpleMathCoreEntry = path.join(extensionRoot, 'math_core', 'main.spl');
const buildMathCoreSimple = process.argv.includes('--build-math-core-simple');
const buildMathCoreRs = process.argv.includes('--build-math-core-rs');

mkdirSync(wasmDir, { recursive: true });
mkdirSync(wasmBuildDir, { recursive: true });

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
        buildFromSimple: true,
        buildFromRust: true,
    },
];

let copiedCount = 0;

for (const artifact of artifacts) {
    const explicitSource = process.env[artifact.envKey]?.trim() || '';
    const inferredSource = defaultBuildDir ? path.join(defaultBuildDir, artifact.buildName) : '';
    let sourcePath = explicitSource || inferredSource;

    if (!sourcePath && artifact.buildFromSimple && buildMathCoreSimple) {
        sourcePath = buildSimpleMathCoreWasmArtifact();
    }

    if (!sourcePath && artifact.buildFromRust && buildMathCoreRs) {
        sourcePath = buildRustMathCoreWasmArtifact();
    }

    if (!sourcePath) {
        const notes = [];
        if (artifact.buildFromSimple) {
            notes.push('--build-math-core-simple');
        }
        if (artifact.buildFromRust) {
            notes.push('--build-math-core-rs');
        }
        const fallbackNote = notes.length > 0
            ? `no ${artifact.envKey}, SIMPLE_VSCODE_WASM_BUILD_DIR, or ${notes.join('/')}`
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

function buildSimpleMathCoreWasmArtifact() {
    if (!existsSync(simpleMathCoreEntry)) {
        throw new Error(`[stage:wasm] Simple math-core entry not found at ${simpleMathCoreEntry}`);
    }

    const simpleBinary = resolveSimpleBinary();
    const builtArtifact = path.join(wasmBuildDir, 'math-core.wasm');
    const compile = spawnSync(
        simpleBinary.command,
        [
            ...simpleBinary.prefixArgs,
            'compile',
            path.relative(repoRoot, simpleMathCoreEntry),
            '--target=wasm32-wasi',
            '-o',
            builtArtifact,
        ],
        {
            cwd: repoRoot,
            encoding: 'utf8',
            stdio: ['ignore', 'pipe', 'pipe'],
        }
    );

    if (compile.status !== 0) {
        const details = [compile.stdout, compile.stderr].filter(Boolean).join('\n').trim();
        throw new Error(
            `[stage:wasm] failed to build pure-Simple math-core wasm.\n${details || 'simple compile returned a non-zero exit code.'}`
        );
    }

    if (!existsSync(builtArtifact)) {
        throw new Error(
            `[stage:wasm] simple compile succeeded, but expected artifact was not found at ${builtArtifact}`
        );
    }

    console.log(`[stage:wasm] built math-core.wasm <- ${builtArtifact}`);
    return builtArtifact;
}

function resolveSimpleBinary() {
    const explicitBinary = process.env.SIMPLE_VSCODE_SIMPLE_BIN?.trim();
    const repoDebugBinary = path.join(repoRoot, 'src', 'compiler_rust', 'target', 'debug', 'simple');
    const repoReleaseBinary = path.join(repoRoot, 'src', 'compiler_rust', 'target', 'release', 'simple');
    const candidates = [
        explicitBinary ? { command: explicitBinary, prefixArgs: [] } : null,
        existsSync(repoDebugBinary) ? { command: repoDebugBinary, prefixArgs: [] } : null,
        existsSync(repoReleaseBinary) ? { command: repoReleaseBinary, prefixArgs: [] } : null,
        { command: 'simple', prefixArgs: [] },
    ].filter(Boolean);

    for (const candidate of candidates) {
        const probe = spawnSync(candidate.command, [...candidate.prefixArgs, '--help'], {
            cwd: repoRoot,
            encoding: 'utf8',
            stdio: ['ignore', 'pipe', 'pipe'],
        });
        if (probe.status === 0) {
            return candidate;
        }
    }

    throw new Error(
        '[stage:wasm] could not find a working `simple` compiler. ' +
        'Set SIMPLE_VSCODE_SIMPLE_BIN or build src/compiler_rust/target/debug/simple first.'
    );
}

function buildRustMathCoreWasmArtifact() {
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
            `[stage:wasm] failed to build Rust math-core wasm crate.\n${details || 'cargo build returned a non-zero exit code.'}`
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

    console.log(`[stage:wasm] built Rust math-core.wasm <- ${builtArtifact}`);
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
