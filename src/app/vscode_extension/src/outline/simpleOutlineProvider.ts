import * as vscode from 'vscode';
import { indexDocumentSymbols, type IndexedSymbol } from '../analysis/simpleAnalysisIndex';

class OutlineItem extends vscode.TreeItem {
    public constructor(
        public readonly document: vscode.TextDocument,
        public readonly symbol: IndexedSymbol,
    ) {
        super(symbol.name, vscode.TreeItemCollapsibleState.None);
        this.description = symbol.detail;
        this.iconPath = new vscode.ThemeIcon('symbol-method');
        this.command = {
            command: 'simple.outline.revealSymbol',
            title: 'Reveal Symbol',
            arguments: [document.uri, symbol.selectionRange],
        };
    }
}

export class SimpleOutlineProvider implements vscode.TreeDataProvider<OutlineItem> {
    private readonly emitter = new vscode.EventEmitter<OutlineItem | undefined | null | void>();
    public readonly onDidChangeTreeData = this.emitter.event;
    private activeDocument: vscode.TextDocument | undefined;

    public setActiveDocument(document: vscode.TextDocument | undefined): void {
        this.activeDocument = document?.languageId === 'simple' || document?.uri.fsPath.endsWith('.spl')
            ? document
            : undefined;
        this.refresh();
    }

    public refresh(): void {
        this.emitter.fire();
    }

    public getTreeItem(element: OutlineItem): vscode.TreeItem {
        return element;
    }

    public getChildren(): OutlineItem[] {
        if (!this.activeDocument) {
            return [];
        }

        return indexDocumentSymbols(this.activeDocument).map((symbol) => new OutlineItem(this.activeDocument!, symbol));
    }
}
