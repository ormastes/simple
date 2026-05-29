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
export declare function createWasmServerOptions(options: WasmLspOptions): Promise<ServerOptions | undefined>;
/**
 * Check if the WASM LSP binary is bundled with the extension.
 */
export declare function isWasmLspAvailable(context: vscode.ExtensionContext, wasmPath: string): Promise<boolean>;
