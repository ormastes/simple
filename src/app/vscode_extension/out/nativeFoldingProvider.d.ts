import * as vscode from 'vscode';
export declare class SimpleFoldingRangeProvider implements vscode.FoldingRangeProvider {
    provideFoldingRanges(document: vscode.TextDocument): vscode.FoldingRange[];
}
