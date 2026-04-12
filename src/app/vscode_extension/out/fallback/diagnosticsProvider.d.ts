import * as vscode from 'vscode';
export declare class SimpleDiagnosticsProvider implements vscode.Disposable {
    private readonly diagnosticCollection;
    private readonly disposables;
    private readonly debounceTimers;
    constructor();
    diagnose(document: vscode.TextDocument): void;
    dispose(): void;
    private debounceDiagnose;
    private checkRenderableBlockSyntax;
    private checkBasicSyntax;
    private checkBrackets;
}
