import * as vscode from 'vscode';
import { detectBlocks } from '../blockDetector';
import { isMathLikeBlock } from '../mathPreview';

interface IndexedSymbol {
    name: string;
    kind: vscode.SymbolKind;
    range: vscode.Range;
    selectionRange: vscode.Range;
    detail: string;
    uri: vscode.Uri;
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

function wordRange(document: vscode.TextDocument, position: vscode.Position): vscode.Range | undefined {
    return document.getWordRangeAtPosition(position, /[A-Za-z_][A-Za-z0-9_]*/);
}

async function collectWorkspaceSymbols(query?: string): Promise<IndexedSymbol[]> {
    const uris = await vscode.workspace.findFiles('**/*.spl', '**/{node_modules,out,.git,target,build}/**', 200);
    const symbols: IndexedSymbol[] = [];
    for (const uri of uris) {
        const document = await vscode.workspace.openTextDocument(uri);
        symbols.push(...indexDocumentSymbols(document));
    }
    if (!query) {
        return symbols;
    }
    const lowered = query.toLowerCase();
    return symbols.filter((symbol) => symbol.name.toLowerCase().includes(lowered));
}

function exactSymbolMatches(symbols: IndexedSymbol[], name: string): IndexedSymbol[] {
    return symbols.filter((symbol) => symbol.name === name);
}

export function indexDocumentSymbols(document: vscode.TextDocument): IndexedSymbol[] {
    const text = document.getText();
    const symbols: IndexedSymbol[] = [];

    for (const pattern of SYMBOL_PATTERNS) {
        pattern.regex.lastIndex = 0;
        let match: RegExpExecArray | null;
        while ((match = pattern.regex.exec(text)) !== null) {
            const symbolName = match[2];
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
            });
        }
    }

    return symbols.sort((left, right) => {
        if (left.uri.toString() !== right.uri.toString()) {
            return left.uri.toString().localeCompare(right.uri.toString());
        }
        return left.range.start.line - right.range.start.line;
    });
}

export class SimpleDocumentSymbolProvider implements vscode.DocumentSymbolProvider {
    public provideDocumentSymbols(document: vscode.TextDocument): vscode.DocumentSymbol[] {
        return indexDocumentSymbols(document).map((symbol) => new vscode.DocumentSymbol(
            symbol.name,
            symbol.detail,
            symbol.kind,
            symbol.range,
            symbol.selectionRange,
        ));
    }
}

export class SimpleWorkspaceSymbolProvider implements vscode.WorkspaceSymbolProvider<vscode.SymbolInformation> {
    public async provideWorkspaceSymbols(query: string): Promise<vscode.SymbolInformation[]> {
        const symbols = await collectWorkspaceSymbols(query);
        return symbols.map((symbol) => new vscode.SymbolInformation(
            symbol.name,
            symbol.kind,
            symbol.detail,
            new vscode.Location(symbol.uri, symbol.selectionRange),
        ));
    }
}

export class SimpleDefinitionProvider implements vscode.DefinitionProvider {
    public async provideDefinition(document: vscode.TextDocument, position: vscode.Position): Promise<vscode.Definition | undefined> {
        const range = wordRange(document, position);
        if (!range) {
            return undefined;
        }

        const word = document.getText(range);
        const currentDocumentHit = indexDocumentSymbols(document).find((symbol) => symbol.name === word);
        if (currentDocumentHit) {
            return new vscode.Location(currentDocumentHit.uri, currentDocumentHit.selectionRange);
        }

        const workspaceHits = await collectWorkspaceSymbols(word);
        const exact = exactSymbolMatches(workspaceHits, word);
        return exact.map((symbol) => new vscode.Location(symbol.uri, symbol.selectionRange));
    }
}

export class SimpleReferenceProvider implements vscode.ReferenceProvider {
    public async provideReferences(
        document: vscode.TextDocument,
        position: vscode.Position,
        context: vscode.ReferenceContext,
    ): Promise<vscode.Location[]> {
        const range = wordRange(document, position);
        if (!range) {
            return [];
        }

        const word = document.getText(range);
        const workspaceHits = exactSymbolMatches(await collectWorkspaceSymbols(word), word);
        const currentDocumentHits = exactSymbolMatches(indexDocumentSymbols(document), word);
        const merged = [...currentDocumentHits, ...workspaceHits];
        const seen = new Set<string>();
        const locations: vscode.Location[] = [];

        for (const symbol of merged) {
            const key = `${symbol.uri.toString()}:${symbol.selectionRange.start.line}:${symbol.selectionRange.start.character}`;
            if (seen.has(key)) {
                continue;
            }
            seen.add(key);
            locations.push(new vscode.Location(symbol.uri, symbol.selectionRange));
        }

        if (context.includeDeclaration) {
            return locations;
        }

        return locations.filter((location) => !location.range.isEqual(range) || location.uri.toString() !== document.uri.toString());
    }
}

export class SimpleHoverProvider implements vscode.HoverProvider {
    public async provideHover(document: vscode.TextDocument, position: vscode.Position): Promise<vscode.Hover | undefined> {
        const offset = document.offsetAt(position);
        const isInsideMath = detectBlocks(document.getText()).some((block) =>
            isMathLikeBlock(block.kind) && offset >= block.from && offset <= block.to,
        );
        if (isInsideMath) {
            return undefined;
        }

        const range = wordRange(document, position);
        if (!range) {
            return undefined;
        }

        const word = document.getText(range);
        const allSymbols = [
            ...indexDocumentSymbols(document),
            ...(await collectWorkspaceSymbols(word)),
        ];
        const symbol = allSymbols.find((candidate) => candidate.name === word);
        if (!symbol) {
            return undefined;
        }

        const markdown = new vscode.MarkdownString(undefined, true);
        markdown.appendMarkdown(`**${symbol.name}**\n\n`);
        markdown.appendMarkdown(`Kind: \`${vscode.SymbolKind[symbol.kind]}\`\n\n`);
        markdown.appendMarkdown(`Source: \`${symbol.uri.fsPath}\`:${symbol.selectionRange.start.line + 1}`);
        return new vscode.Hover(markdown, range);
    }
}
