import * as assert from 'assert';
import * as vscode from 'vscode';

suite('Code Actions Test Suite', () => {
    test('Can provide code actions', async () => {
        const doc = await vscode.workspace.openTextDocument({
            language: 'simple',
            content: 'fn test():\n    let unused = 10\n    pass',
        });

        await vscode.window.showTextDocument(doc);

        // Execute code action provider
        const actions = await vscode.commands.executeCommand<vscode.CodeAction[]>(
            'vscode.executeCodeActionProvider',
            doc.uri,
            new vscode.Range(1, 8, 1, 14) // Range over 'unused'
        );

        // Should provide some code actions (might be refactoring or quick fixes)
        assert.ok(Array.isArray(actions), 'Code actions should be an array');

        await vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Code action has correct properties', () => {
        const action = new vscode.CodeAction(
            'Remove unused variable',
            vscode.CodeActionKind.QuickFix
        );

        action.diagnostics = [
            new vscode.Diagnostic(
                new vscode.Range(1, 8, 1, 14),
                'Variable "unused" is never used',
                vscode.DiagnosticSeverity.Warning
            )
        ];

        assert.strictEqual(action.title, 'Remove unused variable');
        assert.strictEqual(action.kind, vscode.CodeActionKind.QuickFix);
        assert.strictEqual(action.diagnostics?.length, 1);
    });

    test('Can create refactoring code action', () => {
        const action = new vscode.CodeAction(
            'Extract to function',
            vscode.CodeActionKind.Refactor
        );

        action.edit = new vscode.WorkspaceEdit();

        assert.strictEqual(action.title, 'Extract to function');
        assert.strictEqual(action.kind, vscode.CodeActionKind.Refactor);
        assert.ok(action.edit, 'Should have workspace edit');
    });

    test('Can create source action (organize imports)', () => {
        const action = new vscode.CodeAction(
            'Organize Imports',
            vscode.CodeActionKind.SourceOrganizeImports
        );

        assert.strictEqual(action.title, 'Organize Imports');
        assert.strictEqual(action.kind, vscode.CodeActionKind.SourceOrganizeImports);
    });

    test('Code action can have command', () => {
        const action = new vscode.CodeAction(
            'Run formatter',
            vscode.CodeActionKind.Source
        );

        action.command = {
            title: 'Format Document',
            command: 'simple.formatDocument'
        };

        assert.ok(action.command, 'Should have command');
        assert.strictEqual(action.command.command, 'simple.formatDocument');
    });

    test('Can register code action provider', () => {
        let providerDisposable: vscode.Disposable | undefined;

        try {
            const provider: vscode.CodeActionProvider = {
                provideCodeActions(
                    document: vscode.TextDocument,
                    range: vscode.Range | vscode.Selection
                ): vscode.CodeAction[] {
                    const actions: vscode.CodeAction[] = [];

                    // Example: Provide a quick fix for TODO comments
                    if (document.getText(range).includes('TODO')) {
                        const action = new vscode.CodeAction(
                            'Convert TODO to issue',
                            vscode.CodeActionKind.QuickFix
                        );
                        actions.push(action);
                    }

                    return actions;
                }
            };

            providerDisposable = vscode.languages.registerCodeActionsProvider(
                { language: 'simple' },
                provider
            );

            assert.ok(providerDisposable, 'Provider should be registered');
        } finally {
            providerDisposable?.dispose();
        }
    });
});

suite('Document Formatting Test Suite', () => {
    test('Can provide document formatting', async () => {
        const doc = await vscode.workspace.openTextDocument({
            language: 'simple',
            content: 'fn test():\nlet x=10\nreturn x',
        });

        await vscode.window.showTextDocument(doc);

        // Execute formatting provider
        const edits = await vscode.commands.executeCommand<vscode.TextEdit[]>(
            'vscode.executeFormatDocumentProvider',
            doc.uri,
            { tabSize: 4, insertSpaces: true }
        );

        // Formatting provider might return edits
        assert.ok(Array.isArray(edits), 'Formatting edits should be an array');

        await vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Can provide range formatting', async () => {
        const doc = await vscode.workspace.openTextDocument({
            language: 'simple',
            content: 'fn test():\n    let x=10\n    let y=20\n    return x+y',
        });

        await vscode.window.showTextDocument(doc);

        const range = new vscode.Range(1, 0, 2, 12); // Format only lines 1-2

        const edits = await vscode.commands.executeCommand<vscode.TextEdit[]>(
            'vscode.executeFormatRangeProvider',
            doc.uri,
            range,
            { tabSize: 4, insertSpaces: true }
        );

        assert.ok(Array.isArray(edits), 'Range formatting edits should be an array');

        await vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Can register formatting provider', () => {
        let providerDisposable: vscode.Disposable | undefined;

        try {
            const provider: vscode.DocumentFormattingEditProvider = {
                provideDocumentFormattingEdits(
                    document: vscode.TextDocument,
                    options: vscode.FormattingOptions
                ): vscode.TextEdit[] {
                    const edits: vscode.TextEdit[] = [];

                    // Example: Add proper indentation
                    for (let i = 0; i < document.lineCount; i++) {
                        const line = document.lineAt(i);
                        if (line.text.startsWith('fn ') || line.text.startsWith('class ')) {
                            // No indentation for top-level declarations
                        }
                    }

                    return edits;
                }
            };

            providerDisposable = vscode.languages.registerDocumentFormattingEditProvider(
                { language: 'simple' },
                provider
            );

            assert.ok(providerDisposable, 'Formatting provider should be registered');
        } finally {
            providerDisposable?.dispose();
        }
    });

    test('TextEdit has correct properties', () => {
        const range = new vscode.Range(0, 0, 0, 10);
        const edit = new vscode.TextEdit(range, '    ');

        assert.ok(edit.range.isEqual(range), 'Range should match');
        assert.strictEqual(edit.newText, '    ', 'New text should be 4 spaces');
    });

    test('Can create insert, delete, and replace edits', () => {
        // Insert
        const insertEdit = vscode.TextEdit.insert(new vscode.Position(0, 0), 'import std.io\n');
        assert.strictEqual(insertEdit.newText, 'import std.io\n');

        // Delete
        const deleteEdit = vscode.TextEdit.delete(new vscode.Range(1, 0, 2, 0));
        assert.strictEqual(deleteEdit.newText, '');

        // Replace
        const replaceEdit = vscode.TextEdit.replace(
            new vscode.Range(0, 0, 0, 5),
            'function'
        );
        assert.strictEqual(replaceEdit.newText, 'function');
    });
});

suite('Status Bar Test Suite', () => {
    let statusBarItem: vscode.StatusBarItem;

    setup(() => {
        statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 100);
    });

    teardown(() => {
        statusBarItem.dispose();
    });

    test('Can create status bar item', () => {
        assert.ok(statusBarItem, 'Status bar item should be created');
    });

    test('Can set status bar text', () => {
        statusBarItem.text = '$(check) Simple';
        assert.strictEqual(statusBarItem.text, '$(check) Simple');
    });

    test('Can set status bar tooltip', () => {
        statusBarItem.tooltip = 'Simple Language Server';
        assert.strictEqual(statusBarItem.tooltip, 'Simple Language Server');
    });

    test('Can set status bar color', () => {
        statusBarItem.color = '#00FF00';
        assert.strictEqual(statusBarItem.color, '#00FF00');
    });

    test('Can show and hide status bar item', () => {
        statusBarItem.show();
        // No direct way to check if visible, but should not throw
        assert.ok(true);

        statusBarItem.hide();
        assert.ok(true);
    });

    test('Can set status bar command', () => {
        statusBarItem.command = 'simple.showStatus';
        assert.strictEqual(statusBarItem.command, 'simple.showStatus');
    });
});
