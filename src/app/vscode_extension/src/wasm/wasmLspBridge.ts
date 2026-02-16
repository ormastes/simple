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

import * as vscode from 'vscode';
import { ServerOptions } from 'vscode-languageclient/node';
import { getWasiPreopens } from './uriConverter';

export interface WasmLspOptions {
    /** Path to WASM binary relative to extension root */
    wasmPath: string;
    /** Extension context */
    context: vscode.ExtensionContext;
    /** Output channel for LSP logs */
    outputChannel: vscode.OutputChannel;
}

/**
 * Create server options for the WASM-based LSP server.
 *
 * Loads the WASM module and creates a WASI process that communicates
 * via stdin/stdout (LSP protocol).
 *
 * @returns Server options compatible with LanguageClient, or undefined if WASM not available
 */
export async function createWasmServerOptions(
    options: WasmLspOptions
): Promise<ServerOptions | undefined> {
    const { wasmPath, context, outputChannel } = options;

    // Check if @vscode/wasm-wasi is available
    let wasmWasi: any;
    try {
        wasmWasi = await import('@vscode/wasm-wasi');
    } catch {
        outputChannel.appendLine('WASM WASI module not available - falling back to native LSP');
        return undefined;
    }

    // Resolve WASM binary path
    const wasmUri = vscode.Uri.joinPath(context.extensionUri, wasmPath);
    outputChannel.appendLine(`Loading WASM LSP from ${wasmUri.toString()}`);

    // Read WASM binary
    let wasmBytes: Uint8Array;
    try {
        wasmBytes = await vscode.workspace.fs.readFile(wasmUri);
    } catch {
        outputChannel.appendLine(`Failed to read WASM binary at ${wasmUri.toString()}`);
        return undefined;
    }

    // Create WASI process options
    const preopens = getWasiPreopens();
    const processOptions: any = {
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
            kind: 'workspaceFolder' as const,
            mountPoint: p.wasi
        }));
    }

    try {
        // Create WASM/WASI process
        const wasm = await wasmWasi.Wasm.load();
        const wasiProcess = await wasm.createProcess('simple-lsp', wasmBytes, processOptions);

        outputChannel.appendLine('WASM LSP process created successfully');

        // Try to use @vscode/wasm-wasi-lsp for LSP wrapping
        let wasmLsp: any;
        try {
            wasmLsp = await import('@vscode/wasm-wasi-lsp');
        } catch {
            outputChannel.appendLine('WASM WASI LSP module not available');
            return undefined;
        }

        // Create LSP-compatible server options
        return wasmLsp.createServerOptions(wasiProcess);
    } catch (error: any) {
        outputChannel.appendLine(`Failed to create WASM LSP process: ${error.message}`);
        return undefined;
    }
}

/**
 * Check if the WASM LSP binary is bundled with the extension.
 */
export async function isWasmLspAvailable(
    context: vscode.ExtensionContext,
    wasmPath: string
): Promise<boolean> {
    const wasmUri = vscode.Uri.joinPath(context.extensionUri, wasmPath);
    try {
        await vscode.workspace.fs.stat(wasmUri);
        return true;
    } catch {
        return false;
    }
}
