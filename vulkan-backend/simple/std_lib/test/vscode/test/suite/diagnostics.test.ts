import * as assert from 'assert';
import * as vscode from 'vscode';

suite('Diagnostics Test Suite', () => {
    let diagnosticCollection: vscode.DiagnosticCollection;

    suiteSetup(() => {
        // Create a diagnostic collection for testing
        diagnosticCollection = vscode.languages.createDiagnosticCollection('simple');
    });

    suiteTeardown(() => {
        diagnosticCollection.dispose();
    });

    test('Can create diagnostic collection', () => {
        assert.ok(diagnosticCollection, 'Diagnostic collection should be created');
    });

    test('Can add diagnostics to a document', async () => {
        const doc = await vscode.workspace.openTextDocument({
            language: 'simple',
            content: 'fn main():\n    # TODO: implement\n    pass',
        });

        const diagnostics: vscode.Diagnostic[] = [];

        // Add a TODO diagnostic
        const line1 = new vscode.Range(1, 4, 1, 8);
        const diagnostic = new vscode.Diagnostic(
            line1,
            'TODO comments should be resolved before release',
            vscode.DiagnosticSeverity.Information
        );
        diagnostic.source = 'simple-lint';
        diagnostic.code = 'TODO';
        diagnostics.push(diagnostic);

        // Set diagnostics
        diagnosticCollection.set(doc.uri, diagnostics);

        // Verify diagnostics were set
        const setDiagnostics = diagnosticCollection.get(doc.uri);
        assert.strictEqual(setDiagnostics?.length, 1, 'Should have 1 diagnostic');
        assert.strictEqual(setDiagnostics?.[0].message, 'TODO comments should be resolved before release');

        await vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Can create diagnostics with different severities', async () => {
        const doc = await vscode.workspace.openTextDocument({
            language: 'simple',
            content: 'fn test():\n    let x = 10\n    let y = 20',
        });

        const diagnostics: vscode.Diagnostic[] = [];

        // Error diagnostic
        diagnostics.push(new vscode.Diagnostic(
            new vscode.Range(1, 8, 1, 9),
            'Variable "x" is never used',
            vscode.DiagnosticSeverity.Error
        ));

        // Warning diagnostic
        diagnostics.push(new vscode.Diagnostic(
            new vscode.Range(2, 8, 2, 9),
            'Variable "y" is never used',
            vscode.DiagnosticSeverity.Warning
        ));

        diagnosticCollection.set(doc.uri, diagnostics);

        const setDiagnostics = diagnosticCollection.get(doc.uri);
        assert.strictEqual(setDiagnostics?.length, 2, 'Should have 2 diagnostics');

        const errorDiag = setDiagnostics?.find(d => d.severity === vscode.DiagnosticSeverity.Error);
        const warnDiag = setDiagnostics?.find(d => d.severity === vscode.DiagnosticSeverity.Warning);

        assert.ok(errorDiag, 'Should have error diagnostic');
        assert.ok(warnDiag, 'Should have warning diagnostic');

        await vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Can update diagnostics when document changes', async () => {
        const doc = await vscode.workspace.openTextDocument({
            language: 'simple',
            content: 'fn test():\n    pass',
        });

        // Initial diagnostics
        diagnosticCollection.set(doc.uri, [
            new vscode.Diagnostic(
                new vscode.Range(0, 0, 0, 2),
                'Missing type annotation',
                vscode.DiagnosticSeverity.Hint
            )
        ]);

        let diagnostics = diagnosticCollection.get(doc.uri);
        assert.strictEqual(diagnostics?.length, 1, 'Should have 1 initial diagnostic');

        // Update diagnostics
        diagnosticCollection.set(doc.uri, [
            new vscode.Diagnostic(
                new vscode.Range(0, 0, 0, 2),
                'Missing type annotation',
                vscode.DiagnosticSeverity.Hint
            ),
            new vscode.Diagnostic(
                new vscode.Range(1, 4, 1, 8),
                'Empty function body',
                vscode.DiagnosticSeverity.Information
            )
        ]);

        diagnostics = diagnosticCollection.get(doc.uri);
        assert.strictEqual(diagnostics?.length, 2, 'Should have 2 diagnostics after update');

        await vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Can clear diagnostics', async () => {
        const doc = await vscode.workspace.openTextDocument({
            language: 'simple',
            content: 'fn test(): void = pass',
        });

        // Set diagnostics
        diagnosticCollection.set(doc.uri, [
            new vscode.Diagnostic(
                new vscode.Range(0, 0, 0, 2),
                'Test diagnostic',
                vscode.DiagnosticSeverity.Warning
            )
        ]);

        let diagnostics = diagnosticCollection.get(doc.uri);
        assert.strictEqual(diagnostics?.length, 1, 'Should have 1 diagnostic');

        // Clear diagnostics
        diagnosticCollection.delete(doc.uri);

        diagnostics = diagnosticCollection.get(doc.uri);
        assert.strictEqual(diagnostics, undefined, 'Diagnostics should be cleared');

        await vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Diagnostics have correct properties', async () => {
        const doc = await vscode.workspace.openTextDocument({
            language: 'simple',
            content: 'fn main():\n    print("hello")',
        });

        const range = new vscode.Range(0, 0, 0, 2);
        const diagnostic = new vscode.Diagnostic(
            range,
            'Missing return type annotation',
            vscode.DiagnosticSeverity.Warning
        );
        diagnostic.source = 'simple-lint';
        diagnostic.code = 'W001';
        diagnostic.tags = [vscode.DiagnosticTag.Unnecessary];

        diagnosticCollection.set(doc.uri, [diagnostic]);

        const diagnostics = diagnosticCollection.get(doc.uri);
        assert.ok(diagnostics, 'Should have diagnostics');

        const diag = diagnostics![0];
        assert.strictEqual(diag.message, 'Missing return type annotation');
        assert.strictEqual(diag.severity, vscode.DiagnosticSeverity.Warning);
        assert.strictEqual(diag.source, 'simple-lint');
        assert.strictEqual(diag.code, 'W001');
        assert.ok(diag.tags?.includes(vscode.DiagnosticTag.Unnecessary));

        await vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Can handle multiple diagnostic collections', () => {
        const collection1 = vscode.languages.createDiagnosticCollection('simple-syntax');
        const collection2 = vscode.languages.createDiagnosticCollection('simple-semantic');

        assert.ok(collection1, 'Collection 1 should be created');
        assert.ok(collection2, 'Collection 2 should be created');
        assert.notStrictEqual(collection1, collection2, 'Collections should be different');

        collection1.dispose();
        collection2.dispose();
    });
});
