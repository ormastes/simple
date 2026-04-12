/**
 * Rich Custom Editor Provider for Simple language files.
 *
 * Provides a CodeMirror 6-based webview editor with:
 * - Variable line heights (math/images expand lines naturally)
 * - Cursor-aware view mode (non-cursor blocks render as widgets)
 * - Image embedding via img{} blocks
 * - Bi-directional sync with VSCode TextDocument
 */
import * as vscode from 'vscode';
import { type BlockKind } from './blockDetector';
import type { EditorMarkerState } from './testing/editorMarkers';
export interface RenderableBlock {
    kind: BlockKind;
    from: number;
    to: number;
    content: string;
    prefix: string;
    renderedHtml: string;
    imageUri?: string;
    displayMode: 'inline' | 'block';
    status: 'ok' | 'error';
    errorMessage?: string;
}
export declare class RichCustomEditorProvider implements vscode.CustomTextEditorProvider {
    private readonly extensionUri;
    private readonly onActiveDocument?;
    private readonly getMarkerState?;
    static readonly viewType = "simple.richSourceEditor";
    constructor(extensionUri: vscode.Uri, onActiveDocument?: ((document: vscode.TextDocument) => void) | undefined, getMarkerState?: ((documentUri: vscode.Uri) => EditorMarkerState) | undefined);
    resolveCustomTextEditor(document: vscode.TextDocument, webviewPanel: vscode.WebviewPanel, _token: vscode.CancellationToken): Promise<void>;
}
