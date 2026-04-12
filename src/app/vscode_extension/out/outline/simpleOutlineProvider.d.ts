import * as vscode from 'vscode';
import { indexDocumentSymbols } from '../symbols/simpleSymbolProviders';
declare class OutlineItem extends vscode.TreeItem {
    readonly document: vscode.TextDocument;
    readonly symbol: ReturnType<typeof indexDocumentSymbols>[number];
    constructor(document: vscode.TextDocument, symbol: ReturnType<typeof indexDocumentSymbols>[number]);
}
export declare class SimpleOutlineProvider implements vscode.TreeDataProvider<OutlineItem> {
    private readonly emitter;
    readonly onDidChangeTreeData: vscode.Event<void | OutlineItem | null | undefined>;
    private activeDocument;
    setActiveDocument(document: vscode.TextDocument | undefined): void;
    refresh(): void;
    getTreeItem(element: OutlineItem): vscode.TreeItem;
    getChildren(): OutlineItem[];
}
export {};
