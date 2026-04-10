/**
 * Math Sync Panel - webview companion that mirrors the active math block and
 * delegates edits back to the source document.
 *
 * The source editor remains canonical. This panel is a synchronized view with a
 * local source textarea, rendered preview, and edit delegation through normal
 * VS Code document edits so undo/redo and diagnostics stay owned by the editor.
 */
import * as vscode from 'vscode';
import { MathBlockRange, MathDecorationProvider } from './mathDecorationProvider';
export interface MathSyncPanelState {
    documentUri: string;
    blockText: string;
    latex: string;
    pretty: string;
    renderedHtml: string;
    blockLabel: string;
    selectionStart: number;
    selectionEnd: number;
    hasContent: boolean;
}
export declare function findMathBlockAtPosition(provider: MathDecorationProvider, document: vscode.TextDocument, position: vscode.Position): MathBlockRange | undefined;
export declare function replaceRangeInText(text: string, range: vscode.Range, replacement: string): string;
export declare function buildMathSyncPanelHtml(state: MathSyncPanelState, katexCssUri?: string): string;
export declare class MathSyncPanel implements vscode.Disposable {
    static currentPanel: MathSyncPanel | undefined;
    private readonly panel;
    private readonly decorationProvider;
    private readonly extensionUri;
    private readonly katexCssUri;
    private disposables;
    private currentDocumentUri;
    private lastStateKey;
    private syncTimer;
    private constructor();
    static show(decorationProvider: MathDecorationProvider, extensionUri: vscode.Uri): void;
    static isVisible(): boolean;
    static close(): void;
    private handleMessage;
    private handleSelectionChange;
    private handleDocumentChange;
    private scheduleSyncFromEditor;
    private getEditorForCurrentDocument;
    private getCurrentBlock;
    private syncFromEditor;
    dispose(): void;
}
