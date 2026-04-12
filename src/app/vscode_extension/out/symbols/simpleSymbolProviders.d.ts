import * as vscode from 'vscode';
interface IndexedSymbol {
    name: string;
    kind: vscode.SymbolKind;
    range: vscode.Range;
    selectionRange: vscode.Range;
    detail: string;
    uri: vscode.Uri;
}
export declare function indexDocumentSymbols(document: vscode.TextDocument): IndexedSymbol[];
export declare class SimpleDocumentSymbolProvider implements vscode.DocumentSymbolProvider {
    provideDocumentSymbols(document: vscode.TextDocument): vscode.DocumentSymbol[];
}
export declare class SimpleWorkspaceSymbolProvider implements vscode.WorkspaceSymbolProvider<vscode.SymbolInformation> {
    provideWorkspaceSymbols(query: string): Promise<vscode.SymbolInformation[]>;
}
export declare class SimpleDefinitionProvider implements vscode.DefinitionProvider {
    provideDefinition(document: vscode.TextDocument, position: vscode.Position): Promise<vscode.Definition | undefined>;
}
export declare class SimpleReferenceProvider implements vscode.ReferenceProvider {
    provideReferences(document: vscode.TextDocument, position: vscode.Position, context: vscode.ReferenceContext): Promise<vscode.Location[]>;
}
export declare class SimpleHoverProvider implements vscode.HoverProvider {
    provideHover(document: vscode.TextDocument, position: vscode.Position): Promise<vscode.Hover | undefined>;
}
export {};
