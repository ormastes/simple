import * as vscode from 'vscode';
type MathBlockType = 'math' | 'loss' | 'nograd';
interface MathBlockSnapshot {
    blockType: MathBlockType;
    fullStart: number;
    fullEnd: number;
    content: string;
}
type MathRenderStatusKind = 'info' | 'ok' | 'error';
export interface MathCustomEditorState {
    documentUri: string;
    sourceText: string;
    selectionStart: number;
    selectionEnd: number;
    hasActiveBlock: boolean;
    activeBlockLabel: string;
    activeBlockSource: string;
    activeBlockPretty: string;
    activeBlockRenderedHtml: string;
    activeBlockStatusKind: MathRenderStatusKind;
    activeBlockStatusMessage: string;
}
export declare function buildMathCustomEditorState(documentUri: string, sourceText: string, selectionStart: number, selectionEnd: number): MathCustomEditorState;
export declare function detectMathBlocksInSource(text: string): MathBlockSnapshot[];
export declare function findMathBlockAtOffset(text: string, offset: number): MathBlockSnapshot | undefined;
export declare function buildMathCustomEditorHtml(state: MathCustomEditorState, katexCssUri?: string, cspSource?: string): string;
export declare class MathCustomEditorProvider implements vscode.CustomTextEditorProvider {
    private readonly extensionUri;
    static readonly viewType = "simple.mathSourceEditor";
    constructor(extensionUri: vscode.Uri);
    resolveCustomTextEditor(document: vscode.TextDocument, webviewPanel: vscode.WebviewPanel, _token: vscode.CancellationToken): Promise<void>;
}
export {};
