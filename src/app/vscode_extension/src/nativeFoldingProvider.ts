import * as vscode from 'vscode';

function leadingIndent(text: string): number {
    const match = text.match(/^\s*/);
    return match ? match[0].length : 0;
}

function findIndentedBlockEnd(document: vscode.TextDocument, startLine: number, baseIndent: number): number {
    let endLine = startLine;
    for (let line = startLine + 1; line < document.lineCount; line++) {
        const text = document.lineAt(line).text;
        const trimmed = text.trim();
        if (!trimmed) {
            endLine = line;
            continue;
        }
        const indent = leadingIndent(text);
        if (indent <= baseIndent) {
            break;
        }
        endLine = line;
    }
    return endLine;
}

function findTripleStringEnd(document: vscode.TextDocument, startLine: number): number | undefined {
    for (let line = startLine + 1; line < document.lineCount; line++) {
        if (document.lineAt(line).text.includes('"""')) {
            return line;
        }
    }
    return undefined;
}

export class SimpleFoldingRangeProvider implements vscode.FoldingRangeProvider {
    public provideFoldingRanges(document: vscode.TextDocument): vscode.FoldingRange[] {
        const folds: vscode.FoldingRange[] = [];

        for (let line = 0; line < document.lineCount; line++) {
            const text = document.lineAt(line).text;
            const trimmed = text.trim();
            if (!trimmed) {
                continue;
            }

            if (trimmed.startsWith('"""')) {
                const end = findTripleStringEnd(document, line);
                if (typeof end === 'number' && end > line) {
                    folds.push(new vscode.FoldingRange(line, end, vscode.FoldingRangeKind.Region));
                    line = end;
                }
                continue;
            }

            if (!trimmed.endsWith(':')) {
                continue;
            }

            const endLine = findIndentedBlockEnd(document, line, leadingIndent(text));
            if (endLine > line) {
                folds.push(new vscode.FoldingRange(line, endLine, vscode.FoldingRangeKind.Region));
            }
        }

        return folds;
    }
}
