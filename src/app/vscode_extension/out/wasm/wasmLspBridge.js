"use strict";
/**
 * WASM LSP Bridge - Loads .wasm LSP server and wraps as LSP client
 *
 * Uses @vscode/wasm-wasi to create a WASI process from the compiled
 * Simple LSP server WASM module, and @vscode/wasm-wasi-lsp to wrap
 * the WASI process as an LSP client.
 *
 * This enables running the Simple LSP server in VSCode Web (vscode.dev)
 * without any native binary dependencies.
 */
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.createWasmServerOptions = createWasmServerOptions;
exports.isWasmLspAvailable = isWasmLspAvailable;
const vscode = __importStar(require("vscode"));
const uriConverter_1 = require("./uriConverter");
/**
 * Create server options for the WASM-based LSP server.
 *
 * Loads the WASM module and creates a WASI process that communicates
 * via stdin/stdout (LSP protocol).
 *
 * @returns Server options compatible with LanguageClient, or undefined if WASM not available
 */
async function createWasmServerOptions(options) {
    const { wasmPath, context, outputChannel } = options;
    // Check if @vscode/wasm-wasi is available
    let wasmWasi;
    try {
        wasmWasi = await Promise.resolve().then(() => __importStar(require('@vscode/wasm-wasi')));
    }
    catch {
        outputChannel.appendLine('WASM WASI module not available - falling back to native LSP');
        return undefined;
    }
    // Resolve WASM binary path
    const wasmUri = vscode.Uri.joinPath(context.extensionUri, wasmPath);
    outputChannel.appendLine(`Loading WASM LSP from ${wasmUri.toString()}`);
    // Read WASM binary
    let wasmBytes;
    try {
        wasmBytes = await vscode.workspace.fs.readFile(wasmUri);
    }
    catch {
        outputChannel.appendLine(`Failed to read WASM binary at ${wasmUri.toString()}`);
        return undefined;
    }
    // Create WASI process options
    const preopens = (0, uriConverter_1.getWasiPreopens)();
    const processOptions = {
        stdio: {
            in: { kind: 'pipeIn' },
            out: { kind: 'pipeOut' },
            err: { kind: 'pipeOut' }
        },
        args: [],
        env: {
            SIMPLE_RUNTIME_MODE: 'wasi',
            SIMPLE_LSP_DEBUG: '0'
        }
    };
    // Add preopens (workspace directory mapping)
    if (preopens.length > 0) {
        processOptions.mountPoints = preopens.map(p => ({
            kind: 'workspaceFolder',
            mountPoint: p.wasi
        }));
    }
    try {
        // Create WASM/WASI process
        const wasm = await wasmWasi.Wasm.load();
        const wasiProcess = await wasm.createProcess('simple-lsp', wasmBytes, processOptions);
        outputChannel.appendLine('WASM LSP process created successfully');
        // Try to use @vscode/wasm-wasi-lsp for LSP wrapping
        let wasmLsp;
        try {
            wasmLsp = await Promise.resolve().then(() => __importStar(require('@vscode/wasm-wasi-lsp')));
        }
        catch {
            outputChannel.appendLine('WASM WASI LSP module not available');
            return undefined;
        }
        // Create LSP-compatible server options
        return wasmLsp.createServerOptions(wasiProcess);
    }
    catch (error) {
        outputChannel.appendLine(`Failed to create WASM LSP process: ${error.message}`);
        return undefined;
    }
}
/**
 * Check if the WASM LSP binary is bundled with the extension.
 */
async function isWasmLspAvailable(context, wasmPath) {
    const wasmUri = vscode.Uri.joinPath(context.extensionUri, wasmPath);
    try {
        await vscode.workspace.fs.stat(wasmUri);
        return true;
    }
    catch {
        return false;
    }
}
//# sourceMappingURL=wasmLspBridge.js.map