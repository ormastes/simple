"use strict";
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
exports.uriToWasiPath = uriToWasiPath;
exports.wasiPathToUri = wasiPathToUri;
exports.convertDocumentUri = convertDocumentUri;
exports.convertLspUri = convertLspUri;
exports.getWasiPreopens = getWasiPreopens;
const vscode = __importStar(require("vscode"));
/** WASI virtual workspace root */
const WASI_WORKSPACE_ROOT = '/workspace';
/**
 * Convert a VSCode URI to a WASI filesystem path.
 *
 * Examples:
 *   file:///home/user/project/src/main.spl -> /workspace/src/main.spl
 *   vscode-vfs://github/user/repo/src/main.spl -> /workspace/src/main.spl
 */
function uriToWasiPath(uri) {
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
function wasiPathToUri(wasiPath) {
    const workspaceFolder = vscode.workspace.workspaceFolders?.[0];
    if (!workspaceFolder) {
        return undefined;
    }
    // Strip WASI workspace prefix
    let relativePath = wasiPath;
    if (relativePath.startsWith(WASI_WORKSPACE_ROOT + '/')) {
        relativePath = relativePath.substring(WASI_WORKSPACE_ROOT.length + 1);
    }
    else if (relativePath.startsWith(WASI_WORKSPACE_ROOT)) {
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
function convertDocumentUri(uri, isWasm) {
    if (isWasm) {
        return uriToWasiPath(uri);
    }
    return uri.toString();
}
/**
 * Convert an LSP document URI back to a VSCode URI.
 */
function convertLspUri(lspUri, isWasm) {
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
function getWasiPreopens() {
    const preopens = [];
    const workspaceFolder = vscode.workspace.workspaceFolders?.[0];
    if (workspaceFolder) {
        preopens.push({
            host: workspaceFolder.uri.fsPath,
            wasi: WASI_WORKSPACE_ROOT,
        });
    }
    return preopens;
}
//# sourceMappingURL=uriConverter.js.map