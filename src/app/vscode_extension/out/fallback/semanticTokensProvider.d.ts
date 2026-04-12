import * as vscode from 'vscode';
export declare const TOKEN_LEGEND: vscode.SemanticTokensLegend;
export declare class SimpleSemanticTokensProvider implements vscode.DocumentSemanticTokensProvider {
    private readonly emitter;
    readonly onDidChangeSemanticTokens: vscode.Event<void>;
    provideDocumentSemanticTokens(document: vscode.TextDocument): vscode.SemanticTokens;
    private tokenizeLine;
    private findCommentStart;
    private collectStrings;
    private isCovered;
    private markCovered;
}
