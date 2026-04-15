/**
 * Resolves image paths from img{} blocks to webview-safe URIs.
 */

import * as path from 'path';
import * as fs from 'fs';
import * as vscode from 'vscode';

/**
 * Parse the content of an img{} block.
 * Supports: img{"path.png"} or img{path.png}
 */
export function parseImageContent(content: string): { path: string; width?: number; height?: number } | null {
    // Strip surrounding quotes if present
    let imgPath = content.trim();
    if ((imgPath.startsWith('"') && imgPath.endsWith('"')) ||
        (imgPath.startsWith("'") && imgPath.endsWith("'"))) {
        imgPath = imgPath.slice(1, -1);
    }

    if (!imgPath) return null;

    return { path: imgPath };
}

/**
 * Resolve an image path relative to the document, and convert to a webview URI.
 */
export function resolveImageUri(
    imagePath: string,
    documentUri: vscode.Uri,
    webview: vscode.Webview,
): string | null {
    const docDir = vscode.Uri.joinPath(documentUri, '..');

    // Try relative to document directory
    const resolved = vscode.Uri.joinPath(docDir, imagePath);
    const fsPath = resolved.fsPath;

    if (fs.existsSync(fsPath)) {
        return webview.asWebviewUri(resolved).toString();
    }

    // Try workspace folders
    for (const folder of vscode.workspace.workspaceFolders ?? []) {
        const wsResolved = vscode.Uri.joinPath(folder.uri, imagePath);
        if (fs.existsSync(wsResolved.fsPath)) {
            return webview.asWebviewUri(wsResolved).toString();
        }
    }

    return null;
}
