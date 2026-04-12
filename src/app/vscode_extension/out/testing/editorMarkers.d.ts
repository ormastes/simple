import * as vscode from 'vscode';
export interface EditorMarkerState {
    breakpoints: number[];
}
export declare class EditorMarkerManager {
    private readonly states;
    getState(documentUri: vscode.Uri): EditorMarkerState;
    toggleBreakpoint(documentUri: vscode.Uri, line: number): EditorMarkerState;
    private getOrCreateState;
}
