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

/** WASI virtual workspace root */
const WASI_WORKSPACE_ROOT = '/workspace';

/**
 * Convert a VSCode URI to a WASI filesystem path.
 *
 * Examples:
 *   file:///home/user/project/src/main.spl -> /workspace/src/main.spl
 *   vscode-vfs://github/user/repo/src/main.spl -> /workspace/src/main.spl
 */
export function uriToWasiPath(uri: vscode.Uri): string {
    const workspaceFolder = vscode.workspace.workspaceFolders?.[0];

    if (workspaceFolder) {
        // Get relative path from workspace root
        const relativePath = vscode.workspace.asRelativePath(uri, false);
        if (relativePath !== uri.toString()) {
            return `${WASI_WORKSPACE_ROOT}/${relativePath}`;
        }
    }

    // Fallback: use the URI path directly under workspace
    const segments = uri.path.split('/');
    const fileName = segments[segments.length - 1];
    return `${WASI_WORKSPACE_ROOT}/${fileName}`;
}

/**
 * Convert a WASI filesystem path back to a VSCode URI.
 *
 * Examples:
 *   /workspace/src/main.spl -> file:///home/user/project/src/main.spl
 */
export function wasiPathToUri(wasiPath: string): vscode.Uri | undefined {
    const workspaceFolder = vscode.workspace.workspaceFolders?.[0];
    if (!workspaceFolder) {
        return undefined;
    }

    // Strip WASI workspace prefix
    let relativePath = wasiPath;
    if (relativePath.startsWith(WASI_WORKSPACE_ROOT + '/')) {
        relativePath = relativePath.substring(WASI_WORKSPACE_ROOT.length + 1);
    } else if (relativePath.startsWith(WASI_WORKSPACE_ROOT)) {
        relativePath = relativePath.substring(WASI_WORKSPACE_ROOT.length);
    }

    // Construct URI relative to workspace
    return vscode.Uri.joinPath(workspaceFolder.uri, relativePath);
}

/**
 * Convert a document URI to the format expected by LSP.
 *
 * In native mode, URIs pass through unchanged.
 * In WASM mode, URIs are converted to WASI paths.
 */
export function convertDocumentUri(uri: vscode.Uri, isWasm: boolean): string {
    if (isWasm) {
        return uriToWasiPath(uri);
    }
    return uri.toString();
}

/**
 * Convert an LSP document URI back to a VSCode URI.
 */
export function convertLspUri(lspUri: string, isWasm: boolean): vscode.Uri {
    if (isWasm && lspUri.startsWith('/')) {
        const converted = wasiPathToUri(lspUri);
        if (converted) {
            return converted;
        }
    }
    return vscode.Uri.parse(lspUri);
}

/**
 * Build WASI preopens mapping for the workspace.
 *
 * Maps the workspace folder to /workspace in the WASI filesystem.
 */
export function getWasiPreopens(): Array<{ host: string; wasi: string }> {
    const preopens: Array<{ host: string; wasi: string }> = [];

    const workspaceFolder = vscode.workspace.workspaceFolders?.[0];
    if (workspaceFolder) {
        preopens.push({
            host: workspaceFolder.uri.fsPath,
            wasi: WASI_WORKSPACE_ROOT,
        });
    }

    return preopens;
}
