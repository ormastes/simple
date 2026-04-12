"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.SimpleHoverProvider = exports.SimpleDefinitionProvider = exports.SimpleWorkspaceSymbolProvider = exports.SimpleDocumentSymbolProvider = void 0;
exports.indexDocumentSymbols = indexDocumentSymbols;
const vscode = __importStar(require("vscode"));
const SYMBOL_PATTERNS = [
    { regex: /^(\s*)fn\s+([A-Za-z_][A-Za-z0-9_]*)/gm, kind: vscode.SymbolKind.Function, detail: 'fn' },
    { regex: /^(\s*)class\s+([A-Za-z_][A-Za-z0-9_]*)/gm, kind: vscode.SymbolKind.Class, detail: 'class' },
    { regex: /^(\s*)struct\s+([A-Za-z_][A-Za-z0-9_]*)/gm, kind: vscode.SymbolKind.Struct, detail: 'struct' },
    { regex: /^(\s*)enum\s+([A-Za-z_][A-Za-z0-9_]*)/gm, kind: vscode.SymbolKind.Enum, detail: 'enum' },
    { regex: /^(\s*)trait\s+([A-Za-z_][A-Za-z0-9_]*)/gm, kind: vscode.SymbolKind.Interface, detail: 'trait' },
    { regex: /^(\s*)describe\s+"([^"]+)"/gm, kind: vscode.SymbolKind.Namespace, detail: 'describe' },
    { regex: /^(\s*)context\s+"([^"]+)"/gm, kind: vscode.SymbolKind.Namespace, detail: 'context' },
    { regex: /^(\s*)it\s+"([^"]+)"/gm, kind: vscode.SymbolKind.Method, detail: 'it' },
];
function wordRange(document, position) {
    return document.getWordRangeAtPosition(position, /[A-Za-z_][A-Za-z0-9_]*/);
}
async function collectWorkspaceSymbols(query) {
    const uris = await vscode.workspace.findFiles('**/*.spl', '**/{node_modules,out,.git,target,build}/**', 200);
    const symbols = [];
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
function indexDocumentSymbols(document) {
    const text = document.getText();
    const symbols = [];
    for (const pattern of SYMBOL_PATTERNS) {
        pattern.regex.lastIndex = 0;
        let match;
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
class SimpleDocumentSymbolProvider {
    provideDocumentSymbols(document) {
        return indexDocumentSymbols(document).map((symbol) => new vscode.DocumentSymbol(symbol.name, symbol.detail, symbol.kind, symbol.range, symbol.selectionRange));
    }
}
exports.SimpleDocumentSymbolProvider = SimpleDocumentSymbolProvider;
class SimpleWorkspaceSymbolProvider {
    async provideWorkspaceSymbols(query) {
        const symbols = await collectWorkspaceSymbols(query);
        return symbols.map((symbol) => new vscode.SymbolInformation(symbol.name, symbol.kind, symbol.detail, new vscode.Location(symbol.uri, symbol.selectionRange)));
    }
}
exports.SimpleWorkspaceSymbolProvider = SimpleWorkspaceSymbolProvider;
class SimpleDefinitionProvider {
    async provideDefinition(document, position) {
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
        const exact = workspaceHits.filter((symbol) => symbol.name === word);
        return exact.map((symbol) => new vscode.Location(symbol.uri, symbol.selectionRange));
    }
}
exports.SimpleDefinitionProvider = SimpleDefinitionProvider;
class SimpleHoverProvider {
    async provideHover(document, position) {
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
exports.SimpleHoverProvider = SimpleHoverProvider;
//# sourceMappingURL=simpleSymbolProviders.js.map