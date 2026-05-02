/**
 * Fallback Semantic Tokens Provider
 *
 * Provides semantic highlighting for .spl files when the LSP server
 * is not available. Uses regex-based tokenization matching the Simple
 * language syntax.
 */
import * as vscode from 'vscode';
/** Token legend matching package.json semanticTokenTypes */
export declare const TOKEN_LEGEND: vscode.SemanticTokensLegend;
export declare class SimpleSemanticTokensProvider implements vscode.DocumentSemanticTokensProvider {
    private _onDidChangeSemanticTokens;
    readonly onDidChangeSemanticTokens: vscode.Event<void>;
    provideDocumentSemanticTokens(document: vscode.TextDocument): vscode.SemanticTokens;
    notifyChanged(): void;
    private tokenizeLine;
    private findUnquotedHash;
    private tokenizeStrings;
    private isParameter;
    private isAnyCovered;
    private markCovered;
}
