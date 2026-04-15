import * as vscode from 'vscode';
export type EditorMarkerKind = 'breakpoint' | 'bookmark' | 'pointer';
export interface EditorMarkerState {
    breakpoints: number[];
    bookmarks: number[];
    pointerLine: number | null;
}
export declare class EditorMarkerManager implements vscode.Disposable {
    private readonly decorations;
    private readonly states;
    private readonly disposables;
    constructor();
    toggleBreakpoint(editor: vscode.TextEditor): void;
    toggleBookmark(editor: vscode.TextEditor): void;
    togglePointer(editor: vscode.TextEditor): void;
    clearPointer(editor: vscode.TextEditor): void;
    jumpToNextBookmark(editor: vscode.TextEditor): void;
    jumpToPreviousBookmark(editor: vscode.TextEditor): void;
    refresh(editor: vscode.TextEditor): void;
    getState(documentUri: vscode.Uri): EditorMarkerState;
    dispose(): void;
    private getOrCreateState;
    private toggleLine;
    private jumpToBookmark;
}
