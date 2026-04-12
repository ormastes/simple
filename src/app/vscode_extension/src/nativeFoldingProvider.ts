import * as vscode from 'vscode';
import { collectFoldingRanges } from './analysis/simpleAnalysisIndex';

export class SimpleFoldingRangeProvider implements vscode.FoldingRangeProvider {
    public provideFoldingRanges(document: vscode.TextDocument): vscode.FoldingRange[] {
        return collectFoldingRanges(document);
    }
}
