import * as vscode from 'vscode';
import { ExtensionHostServices } from '../services/extensionHostServices';
import { SimpleCliService } from '../services/simpleCliService';
import { detectTestBlocks, type TestBlock } from './testDiscovery';

function createTestId(uri: vscode.Uri, label: string, line: number): string {
    return `${uri.toString()}::${label}::${line}`;
}

function isDoctestBlock(block: TestBlock): boolean {
    return block.kind === 'sdoctest';
}

function collectItems(collection: vscode.TestItemCollection): vscode.TestItem[] {
    const items: vscode.TestItem[] = [];
    collection.forEach((item) => {
        items.push(item);
    });
    return items;
}

export class SimpleTestController implements vscode.Disposable {
    private readonly controller: vscode.TestController;
    private readonly output = vscode.window.createOutputChannel('Simple Test Runner');
    private readonly profile: vscode.TestRunProfile;
    private readonly disposables: vscode.Disposable[] = [];

    public constructor(
        private readonly cli: SimpleCliService,
        private readonly services: ExtensionHostServices,
    ) {
        this.controller = vscode.tests.createTestController('simpleTests', 'Simple Tests');
        this.controller.resolveHandler = async (item) => {
            if (item) {
                await this.refreshUri(item.uri ?? vscode.Uri.parse(item.id.split('::')[0]));
                return;
            }
            await this.refreshWorkspace();
        };
        this.profile = this.controller.createRunProfile(
            'Run',
            vscode.TestRunProfileKind.Run,
            (request, token) => void this.runTests(request, token),
            true,
        );

        this.disposables.push(
            this.controller,
            this.profile,
            this.output,
            vscode.workspace.onDidOpenTextDocument((document) => {
                if (document.languageId === 'simple') {
                    void this.refreshDocument(document);
                }
            }),
            vscode.workspace.onDidChangeTextDocument((event) => {
                if (event.document.languageId === 'simple') {
                    void this.refreshDocument(event.document);
                }
            }),
            vscode.workspace.onDidDeleteFiles((event) => {
                for (const uri of event.files) {
                    this.controller.items.delete(uri.toString());
                }
            }),
        );

        for (const document of vscode.workspace.textDocuments) {
            if (document.languageId === 'simple') {
                void this.refreshDocument(document);
            }
        }
    }

    public getController(): vscode.TestController {
        return this.controller;
    }

    public async refreshWorkspace(): Promise<void> {
        const uris = await vscode.workspace.findFiles('**/*.spl', '**/{node_modules,out,.git,target,build}/**', 200);
        for (const uri of uris) {
            await this.refreshUri(uri);
        }
    }

    public dispose(): void {
        for (const disposable of this.disposables) {
            disposable.dispose();
        }
    }

    private async refreshUri(uri: vscode.Uri): Promise<void> {
        try {
            const document = await vscode.workspace.openTextDocument(uri);
            await this.refreshDocument(document);
        } catch {
            this.controller.items.delete(uri.toString());
        }
    }

    private async refreshDocument(document: vscode.TextDocument): Promise<void> {
        if (document.languageId !== 'simple') {
            return;
        }

        const fileId = document.uri.toString();
        const fileItem = this.controller.items.get(fileId)
            ?? this.controller.createTestItem(fileId, document.fileName.split(/[\\/]/).pop() ?? document.fileName, document.uri);
        fileItem.canResolveChildren = false;
        this.controller.items.add(fileItem);
        fileItem.children.replace([]);

        for (const block of detectTestBlocks(document)) {
            if (!isDoctestBlock(block)) {
                continue;
            }
            const child = this.controller.createTestItem(
                createTestId(document.uri, block.label, block.line),
                block.label,
                document.uri,
            );
            child.range = new vscode.Range(block.line, 0, block.line, document.lineAt(block.line).text.length);
            fileItem.children.add(child);
        }
    }

    private async runTests(request: vscode.TestRunRequest, token: vscode.CancellationToken): Promise<void> {
        const run = this.controller.createTestRun(request);
        const fileItems = this.collectFileItems(request);

        try {
            this.services.setStatus('tests', { health: 'starting', source: 'native', message: 'Running Simple tests' });
            for (const fileItem of fileItems) {
                await this.runFileItem(fileItem, run, token);
            }
            this.services.markReady('tests', `Ran ${fileItems.length} test file(s)`);
        } catch (error) {
            const detail = error instanceof Error ? error.message : String(error);
            this.services.markDegraded('tests', 'Test run failed', 'native', detail);
        } finally {
            run.end();
        }
    }

    private collectFileItems(request: vscode.TestRunRequest): vscode.TestItem[] {
        const included = request.include && request.include.length > 0
            ? request.include
            : collectItems(this.controller.items);
        const fileMap = new Map<string, vscode.TestItem>();

        for (const item of included) {
            const fileItem = item.parent ?? item;
            fileMap.set(fileItem.id, fileItem);
        }

        return Array.from(fileMap.values()).filter((item) => item.uri);
    }

    private async runFileItem(fileItem: vscode.TestItem, run: vscode.TestRun, token: vscode.CancellationToken): Promise<void> {
        const childItems = collectItems(fileItem.children);
        run.enqueued(fileItem);
        run.started(fileItem);
        for (const child of childItems) {
            run.enqueued(child);
            run.started(child);
        }

        const hasDoctestOnlyChildren = childItems.length > 0 && childItems.every((child) => child.label === 'sdoctest');
        const args = hasDoctestOnlyChildren
            ? ['test', '--sdoctest', fileItem.uri!.fsPath]
            : ['test', fileItem.uri!.fsPath];

        const result = await this.cli.run(args, {
            cwd: vscode.workspace.workspaceFolders?.[0]?.uri.fsPath,
            token,
            resolveFrom: fileItem.uri!.fsPath,
        });
        const duration = Math.max(1, result.combined.length > 0 ? result.combined.length : 1);
        this.output.appendLine(`$ simple ${args.join(' ')}`);
        if (result.stdout.trim()) {
            this.output.appendLine(result.stdout.trim());
        }
        if (result.stderr.trim()) {
            this.output.appendLine(result.stderr.trim());
        }
        run.appendOutput(`${result.combined || '(no output)'}\n`, undefined, fileItem);

        if (result.exitCode === 0) {
            run.passed(fileItem, duration);
            for (const child of childItems) {
                run.passed(child, duration);
            }
        } else {
            const message = new vscode.TestMessage(result.combined || 'Simple test command failed');
            run.failed(fileItem, message, duration);
            for (const child of childItems) {
                run.failed(child, message, duration);
            }
        }
    }
}
