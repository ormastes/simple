/**
 * Test CodeLens Provider
 *
 * Shows "▶ Run Test" / "▶ Run File" CodeLens above:
 * - `describe "...":`  - SSpec test groups
 * - `it "...":`        - Individual test examples
 * - `context "...":`   - Test context groups
 * - `""" sdoctest:`    - Inline documentation tests
 *
 * Runs tests via `bin/simple test <file>` in the integrated terminal.
 * Runs sdoctests via `bin/simple test --sdoctest <file>`.
 */
import * as vscode from 'vscode';
export declare class TestCodeLensProvider implements vscode.CodeLensProvider, vscode.Disposable {
    private disposables;
    private _onDidChangeCodeLenses;
    readonly onDidChangeCodeLenses: vscode.Event<void>;
    constructor();
    provideCodeLenses(document: vscode.TextDocument, _token: vscode.CancellationToken): vscode.CodeLens[];
    /**
     * Detect all test blocks and sdoctest markers in a document.
     */
    private detectTestBlocks;
    dispose(): void;
}
/**
 * Run test file in integrated terminal.
 */
export declare function runTestFile(uri: vscode.Uri): void;
/**
 * Run sdoctest for a file in integrated terminal.
 */
export declare function runSdoctest(uri: vscode.Uri): void;
/**
 * Run test for the file currently open in the active editor.
 */
export declare function runTestAtCursor(): void;
