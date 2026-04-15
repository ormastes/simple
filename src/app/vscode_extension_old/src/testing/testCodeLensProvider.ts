/**
 * Test CodeLens Provider
 *
 * Shows "▶ Run Test" / "▶ Run File" CodeLens above:
 * - `describe "...":`  - SSpec test groups
 * - `it "...":`        - Individual test examples
 * - `context "...":`   - Test context groups
 * - `""" sdoctest:`    - Inline documentation tests
 *
 * Runs tests via `bin/simple test <file>` in the integrated terminal.
 * Runs sdoctests via `bin/simple test --sdoctest <file>`.
 */

import * as vscode from 'vscode';

/** Regex patterns for test block detection */
const DESCRIBE_RE = /^(\s*)(describe)\s+"([^"]+)":/;
const CONTEXT_RE = /^(\s*)(context)\s+"([^"]+)":/;
const IT_RE = /^(\s*)(it)\s+"([^"]+)":/;
const SDOCTEST_RE = /^\s*"""\s*sdoctest:/;

/** Type of test block detected */
type TestBlockKind = 'describe' | 'context' | 'it' | 'sdoctest';

interface TestBlock {
    kind: TestBlockKind;
    label: string;
    line: number;
}

export class TestCodeLensProvider implements vscode.CodeLensProvider, vscode.Disposable {
    private disposables: vscode.Disposable[] = [];
    private _onDidChangeCodeLenses = new vscode.EventEmitter<void>();
    public readonly onDidChangeCodeLenses = this._onDidChangeCodeLenses.event;

    constructor() {
        // Refresh CodeLenses when document changes
        this.disposables.push(
            vscode.workspace.onDidChangeTextDocument(() => {
                this._onDidChangeCodeLenses.fire();
            })
        );
    }

    provideCodeLenses(
        document: vscode.TextDocument,
        _token: vscode.CancellationToken
    ): vscode.CodeLens[] {
        if (document.languageId !== 'simple') {
            return [];
        }

        const lenses: vscode.CodeLens[] = [];
        const blocks = this.detectTestBlocks(document);

        for (const block of blocks) {
            const range = new vscode.Range(block.line, 0, block.line, 0);

            if (block.kind === 'sdoctest') {
                // SDoctest: Run Doctest
                lenses.push(new vscode.CodeLens(range, {
                    title: '$(play) Run Doctest',
                    command: 'simple.test.runSdoctest',
                    arguments: [document.uri],
                    tooltip: `Run sdoctest in ${document.fileName}`,
                }));
            } else if (block.kind === 'describe') {
                // describe: Run File + Run Test
                lenses.push(new vscode.CodeLens(range, {
                    title: '$(play) Run File',
                    command: 'simple.test.runFile',
                    arguments: [document.uri],
                    tooltip: `Run all tests in ${document.fileName}`,
                }));
            } else {
                // it / context: Run Test (runs the file, since no --filter exists yet)
                lenses.push(new vscode.CodeLens(range, {
                    title: '$(play) Run Test',
                    command: 'simple.test.runFile',
                    arguments: [document.uri],
                    tooltip: `Run tests in ${document.fileName}`,
                }));
            }
        }

        return lenses;
    }

    /**
     * Detect all test blocks and sdoctest markers in a document.
     */
    private detectTestBlocks(document: vscode.TextDocument): TestBlock[] {
        const blocks: TestBlock[] = [];

        for (let i = 0; i < document.lineCount; i++) {
            const lineText = document.lineAt(i).text;

            let match = lineText.match(DESCRIBE_RE);
            if (match) {
                blocks.push({ kind: 'describe', label: match[3], line: i });
                continue;
            }

            match = lineText.match(CONTEXT_RE);
            if (match) {
                blocks.push({ kind: 'context', label: match[3], line: i });
                continue;
            }

            match = lineText.match(IT_RE);
            if (match) {
                blocks.push({ kind: 'it', label: match[3], line: i });
                continue;
            }

            if (SDOCTEST_RE.test(lineText)) {
                blocks.push({ kind: 'sdoctest', label: 'sdoctest', line: i });
            }
        }

        return blocks;
    }

    dispose(): void {
        this._onDidChangeCodeLenses.dispose();
        for (const d of this.disposables) {
            d.dispose();
        }
        this.disposables = [];
    }
}

/**
 * Run test file in integrated terminal.
 */
export function runTestFile(uri: vscode.Uri): void {
    const config = vscode.workspace.getConfiguration('simple');
    const simplePath = config.get<string>('lsp.serverPath', 'simple');
    const filePath = uri.fsPath;

    const terminal = getOrCreateTestTerminal();
    terminal.show(true);
    terminal.sendText(`${simplePath} test "${filePath}"`);
}

/**
 * Run sdoctest for a file in integrated terminal.
 */
export function runSdoctest(uri: vscode.Uri): void {
    const config = vscode.workspace.getConfiguration('simple');
    const simplePath = config.get<string>('lsp.serverPath', 'simple');
    const filePath = uri.fsPath;

    const terminal = getOrCreateTestTerminal();
    terminal.show(true);
    terminal.sendText(`${simplePath} test --sdoctest "${filePath}"`);
}

/**
 * Run test for the file currently open in the active editor.
 */
export function runTestAtCursor(): void {
    const editor = vscode.window.activeTextEditor;
    if (!editor || editor.document.languageId !== 'simple') {
        vscode.window.showWarningMessage('No Simple file is active');
        return;
    }
    runTestFile(editor.document.uri);
}

/** Reuse or create a terminal for test output */
function getOrCreateTestTerminal(): vscode.Terminal {
    const name = 'Simple Tests';
    const existing = vscode.window.terminals.find(t => t.name === name);
    if (existing) {
        return existing;
    }
    return vscode.window.createTerminal(name);
}
