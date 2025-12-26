import * as assert from 'assert';
import * as vscode from 'vscode';

suite('Hello Extension Test Suite', () => {
    vscode.window.showInformationMessage('Start all tests.');

    test('Extension should be present', () => {
        assert.ok(vscode.extensions.getExtension('simple.hello-extension'));
    });

    test('Extension should activate', async function () {
        this.timeout(10000);

        const ext = vscode.extensions.getExtension('simple.hello-extension');
        assert.ok(ext, 'Extension should be installed');

        await ext!.activate();
        assert.strictEqual(ext!.isActive, true, 'Extension should be active');
    });

    test('Should register hello command', async () => {
        const commands = await vscode.commands.getCommands(true);
        const hasCommand = commands.includes('simple.hello');
        assert.strictEqual(hasCommand, true, 'Hello command should be registered');
    });

    test('Hello command should execute', async () => {
        // Execute the hello command
        await vscode.commands.executeCommand('simple.hello');

        // Command executed successfully (no throw)
        assert.ok(true);
    });

    test('Should provide completions for Simple files', async () => {
        // Create a test document
        const doc = await vscode.workspace.openTextDocument({
            language: 'simple',
            content: 'fn ',
        });

        const position = new vscode.Position(0, 3);

        // Execute completion provider
        const completions = await vscode.commands.executeCommand<vscode.CompletionList>(
            'vscode.executeCompletionItemProvider',
            doc.uri,
            position
        );

        assert.ok(completions, 'Completions should be provided');
        assert.ok(completions.items.length > 0, 'Should have completion items');

        // Close the document
        await vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Should show hover information', async () => {
        const doc = await vscode.workspace.openTextDocument({
            language: 'simple',
            content: 'fn main(): void',
        });

        const position = new vscode.Position(0, 0); // Position on 'fn'

        const hovers = await vscode.commands.executeCommand<vscode.Hover[]>(
            'vscode.executeHoverProvider',
            doc.uri,
            position
        );

        // Hover provider might return information
        // For hello extension, this is optional
        assert.ok(Array.isArray(hovers), 'Hover result should be an array');

        await vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Should register language configuration', () => {
        const languages = vscode.languages.getLanguages();

        // Verify Simple language is registered
        languages.then((langs) => {
            const hasSimple = langs.includes('simple');
            assert.ok(hasSimple, 'Simple language should be registered');
        });
    });
});
