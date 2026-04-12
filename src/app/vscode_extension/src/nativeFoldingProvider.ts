import * as vscode from 'vscode';
import { analyzeDocument } from './analysis/simpleAnalysisIndex';

export class SimpleFoldingRangeProvider implements vscode.FoldingRangeProvider {
    public provideFoldingRanges(document: vscode.TextDocument): vscode.FoldingRange[] {
        return analyzeDocument(document).folds;
    }
}
