import * as vscode from 'vscode';

export interface IndexedSymbol {
    name: string;
    kind: vscode.SymbolKind;
    range: vscode.Range;
    selectionRange: vscode.Range;
    detail: string;
    uri: vscode.Uri;
    indent: number;
}

export type TestBlockKind = 'describe' | 'context' | 'it' | 'sdoctest';

export interface TestBlock {
    kind: TestBlockKind;
    label: string;
    line: number;
    indent: number;
}

const SYMBOL_PATTERNS: Array<{
    regex: RegExp;
    kind: vscode.SymbolKind;
    detail: string;
}> = [
    { regex: /^(\s*)fn\s+([A-Za-z_][A-Za-z0-9_]*)/gm, kind: vscode.SymbolKind.Function, detail: 'fn' },
    { regex: /^(\s*)class\s+([A-Za-z_][A-Za-z0-9_]*)/gm, kind: vscode.SymbolKind.Class, detail: 'class' },
    { regex: /^(\s*)struct\s+([A-Za-z_][A-Za-z0-9_]*)/gm, kind: vscode.SymbolKind.Struct, detail: 'struct' },
    { regex: /^(\s*)enum\s+([A-Za-z_][A-Za-z0-9_]*)/gm, kind: vscode.SymbolKind.Enum, detail: 'enum' },
    { regex: /^(\s*)trait\s+([A-Za-z_][A-Za-z0-9_]*)/gm, kind: vscode.SymbolKind.Interface, detail: 'trait' },
    { regex: /^(\s*)describe\s+"([^"]+)"/gm, kind: vscode.SymbolKind.Namespace, detail: 'describe' },
    { regex: /^(\s*)context\s+"([^"]+)"/gm, kind: vscode.SymbolKind.Namespace, detail: 'context' },
    { regex: /^(\s*)it\s+"([^"]+)"/gm, kind: vscode.SymbolKind.Method, detail: 'it' },
];

const DESCRIBE_RE = /^(\s*)(describe)\s+"([^"]+)":/;
const CONTEXT_RE = /^(\s*)(context)\s+"([^"]+)":/;
const IT_RE = /^(\s*)(it)\s+"([^"]+)":/;
const SDOCTEST_RE = /^\s*"""\s*sdoctest:/;

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

export function indexDocumentSymbols(document: vscode.TextDocument): IndexedSymbol[] {
    const text = document.getText();
    const symbols: IndexedSymbol[] = [];

    for (const pattern of SYMBOL_PATTERNS) {
        pattern.regex.lastIndex = 0;
        let match: RegExpExecArray | null;
        while ((match = pattern.regex.exec(text)) !== null) {
            const symbolName = match[2];
            const indent = match[1]?.length ?? 0;
            const start = document.positionAt(match.index + match[0].lastIndexOf(symbolName));
            const end = start.translate(0, symbolName.length);
            const line = document.lineAt(start.line);
            symbols.push({
                name: symbolName,
                kind: pattern.kind,
                range: line.range,
                selectionRange: new vscode.Range(start, end),
                detail: pattern.detail,
                uri: document.uri,
                indent,
            });
        }
    }

    return symbols.sort((left, right) => left.range.start.line - right.range.start.line);
}

export function detectTestBlocks(document: vscode.TextDocument): TestBlock[] {
    const blocks: TestBlock[] = [];
    for (let line = 0; line < document.lineCount; line++) {
        const text = document.lineAt(line).text;
        let match = text.match(DESCRIBE_RE);
        if (match) {
            blocks.push({ kind: 'describe', label: match[3], line, indent: match[1].length });
            continue;
        }

        match = text.match(CONTEXT_RE);
        if (match) {
            blocks.push({ kind: 'context', label: match[3], line, indent: match[1].length });
            continue;
        }

        match = text.match(IT_RE);
        if (match) {
            blocks.push({ kind: 'it', label: match[3], line, indent: match[1].length });
            continue;
        }

        if (SDOCTEST_RE.test(text)) {
            blocks.push({ kind: 'sdoctest', label: 'sdoctest', line, indent: leadingIndent(text) });
        }
    }
    return blocks;
}

export function collectFoldingRanges(document: vscode.TextDocument): vscode.FoldingRange[] {
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
