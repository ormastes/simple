/**
 * URI Converter - Translates between VSCode URIs and WASI filesystem paths
 *
 * VSCode uses URIs like:
 *   - file:///home/user/project/src/main.spl (desktop)
 *   - vscode-vfs://github/user/repo/src/main.spl (web)
 *
 * WASI sees a virtual filesystem:
 *   - /workspace/src/main.spl
 *
 * This module handles the bidirectional mapping.
 */
import * as vscode from 'vscode';
/**
 * Convert a VSCode URI to a WASI filesystem path.
 *
 * Examples:
 *   file:///home/user/project/src/main.spl -> /workspace/src/main.spl
 *   vscode-vfs://github/user/repo/src/main.spl -> /workspace/src/main.spl
 */
export declare function uriToWasiPath(uri: vscode.Uri): string;
/**
 * Convert a WASI filesystem path back to a VSCode URI.
 *
 * Examples:
 *   /workspace/src/main.spl -> file:///home/user/project/src/main.spl
 */
export declare function wasiPathToUri(wasiPath: string): vscode.Uri | undefined;
/**
 * Convert a document URI to the format expected by LSP.
 *
 * In native mode, URIs pass through unchanged.
 * In WASM mode, URIs are converted to WASI paths.
 */
export declare function convertDocumentUri(uri: vscode.Uri, isWasm: boolean): string;
/**
 * Convert an LSP document URI back to a VSCode URI.
 */
export declare function convertLspUri(lspUri: string, isWasm: boolean): vscode.Uri;
/**
 * Build WASI preopens mapping for the workspace.
 *
 * Maps the workspace folder to /workspace in the WASI filesystem.
 */
export declare function getWasiPreopens(): Array<{
    host: string;
    wasi: string;
}>;
