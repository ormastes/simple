/**
 * Fallback Diagnostics Provider
 *
 * Provides basic syntax error detection for .spl files when the LSP
 * server is not available. Detects unclosed brackets, basic syntax
 * errors, and structural issues.
 */
import * as vscode from 'vscode';
export declare class SimpleDiagnosticsProvider implements vscode.Disposable {
    private diagnosticCollection;
    private disposables;
    private debounceTimers;
    constructor();
    private debounceDiagnose;
    diagnose(document: vscode.TextDocument): void;
    private checkBrackets;
    private checkBasicSyntax;
    dispose(): void;
}
