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

        return detectTestBlocks(document).map((block) => {
            const range = new vscode.Range(block.line, 0, block.line, 0);
            const command = block.kind === 'sdoctest' ? 'simple.test.runSdoctest' : 'simple.test.runFile';
            const title = block.kind === 'sdoctest'
                ? '$(play) Run Doctest'
                : block.kind === 'describe'
                    ? '$(play) Run File'
                    : '$(play) Run Test';
            return new vscode.CodeLens(range, {
                title,
                command,
                arguments: [document.uri],
                tooltip: `Run ${block.kind} from ${document.fileName}`,
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
