import * as vscode from 'vscode';
import { detectTestBlocks } from './testDiscovery';

export class TestCodeLensProvider implements vscode.CodeLensProvider, vscode.Disposable {
    private readonly disposables: vscode.Disposable[] = [];
    private readonly emitter = new vscode.EventEmitter<void>();
    public readonly onDidChangeCodeLenses = this.emitter.event;

    public constructor() {
        this.disposables.push(
            vscode.workspace.onDidChangeTextDocument(() => this.emitter.fire()),
        );
    }

    public provideCodeLenses(document: vscode.TextDocument): vscode.CodeLens[] {
        if (document.languageId !== 'simple') {
            return [];
        }

        return detectTestBlocks(document)
            .filter((block) => block.runnableScope === 'file' || block.runnableScope === 'doctest')
            .map((block) => {
            const range = new vscode.Range(block.line, 0, block.line, 0);
            const command = block.runnableScope === 'doctest' ? 'simple.test.runSdoctest' : 'simple.test.runFile';
            const title = block.runnableScope === 'doctest'
                ? '$(play) Run Doctest'
                : '$(play) Run File';
            return new vscode.CodeLens(range, {
                title,
                command,
                arguments: [document.uri],
                tooltip: block.runnableScope === 'doctest'
                    ? `Run doctests from ${document.fileName}`
                    : `Run ${document.fileName} from this scope`,
            });
        });
    }

    public dispose(): void {
        this.emitter.dispose();
        for (const disposable of this.disposables) {
            disposable.dispose();
        }
    }
}
