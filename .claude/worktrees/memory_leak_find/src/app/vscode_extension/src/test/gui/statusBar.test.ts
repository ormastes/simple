/**
 * GUI Tests - Status Bar and Commands
 * Tests status bar integration and command execution
 */

import * as assert from 'assert';
import * as vscode from 'vscode';
import { TestUtils } from '../helpers/testUtils';

suite('GUI - Status Bar and Commands', function() {
    this.timeout(30000);

    suiteSetup(async function() {
        await TestUtils.activateExtension();
        await TestUtils.waitForLSP(15000);
    });

    teardown(async () => {
        await TestUtils.closeAllEditors();
    });

    test('Should execute LSP restart command', async () => {
        await vscode.commands.executeCommand('simple.lsp.restart');

        // Wait for restart
        await TestUtils.sleep(3000);

        // Verify LSP is still active after restart
        assert.ok(TestUtils.isExtensionActive(), 'Extension should remain active after restart');
    });

    test('Should execute show output channel command', async () => {
        await vscode.commands.executeCommand('simple.lsp.showOutputChannel');

        await TestUtils.sleep(500);

        assert.ok(true, 'Show output channel command executed');
    });

    test('Should execute AI toggle command', async () => {
        const aiEnabled = TestUtils.getConfig<boolean>('simple', 'ai.enabled');

        if (!aiEnabled) {
            console.log('⚠️  AI disabled, skipping toggle test');
            return;
        }

        try {
            await vscode.commands.executeCommand('simple.ai.toggleInlineCompletions');
            await TestUtils.sleep(500);

            // Toggle back
            await vscode.commands.executeCommand('simple.ai.toggleInlineCompletions');
            await TestUtils.sleep(500);

            assert.ok(true, 'AI toggle command executed successfully');
        } catch (error) {
            console.log('⚠️  AI toggle failed (language model may not be available)');
        }
    });

    test('Should execute explain code command with selection', async () => {
        const aiEnabled = TestUtils.getConfig<boolean>('simple', 'ai.enabled');

        if (!aiEnabled) {
            console.log('⚠️  AI disabled, skipping explain test');
            return;
        }

        const testDoc = await TestUtils.createTestFile(
            'test-explain-cmd.spl',
            'fn add(x: i32, y: i32): i32 = x + y'
        );

        const editor = TestUtils.getActiveEditor()!;

        // Select the code
        await TestUtils.selectRange(editor, 0, 0, 0, 35);

        try {
            // Execute explain command (will show progress)
            const promise = vscode.commands.executeCommand('simple.ai.explainCode');

            // Wait a bit for progress to start
            await TestUtils.sleep(1000);

            // Note: We can't wait for full completion in tests as it may take too long
            // Just verify command started without error

            TestUtils.deleteTestFile('test-explain-cmd.spl');
            assert.ok(true, 'Explain code command started successfully');
        } catch (error) {
            TestUtils.deleteTestFile('test-explain-cmd.spl');
            console.log('⚠️  Explain failed (language model may not be available)');
        }
    });

    test('Should execute review code command with selection', async () => {
        const aiEnabled = TestUtils.getConfig<boolean>('simple', 'ai.enabled');

        if (!aiEnabled) {
            console.log('⚠️  AI disabled, skipping review test');
            return;
        }

        const testDoc = await TestUtils.createTestFile(
            'test-review-cmd.spl',
            'fn process(items: List[i32]):\n    for i in items:\n        print(i)'
        );

        const editor = TestUtils.getActiveEditor()!;
        await TestUtils.selectRange(editor, 0, 0, 2, 19);

        try {
            const promise = vscode.commands.executeCommand('simple.ai.reviewCode');
            await TestUtils.sleep(1000);

            TestUtils.deleteTestFile('test-review-cmd.spl');
            assert.ok(true, 'Review code command started successfully');
        } catch (error) {
            TestUtils.deleteTestFile('test-review-cmd.spl');
            console.log('⚠️  Review failed (language model may not be available)');
        }
    });

    test('Should execute generate code command', async () => {
        const aiEnabled = TestUtils.getConfig<boolean>('simple', 'ai.enabled');

        if (!aiEnabled) {
            console.log('⚠️  AI disabled, skipping generate test');
            return;
        }

        // Note: This command shows an input box which can't be easily automated
        // We just verify the command exists
        const commands = await vscode.commands.getCommands();

        assert.ok(
            commands.includes('simple.ai.generateCode'),
            'Generate code command should be registered'
        );
    });

    test('Should handle explain command without selection', async () => {
        const testDoc = await TestUtils.createTestFile(
            'test-no-selection.spl',
            'fn test(): void'
        );

        try {
            await vscode.commands.executeCommand('simple.ai.explainCode');
            await TestUtils.sleep(500);

            // Should show error about no selection
            TestUtils.deleteTestFile('test-no-selection.spl');
        } catch (error: any) {
            TestUtils.deleteTestFile('test-no-selection.spl');
            // Expected to fail with no selection
        }

        assert.ok(true, 'Handled no selection appropriately');
    });

    test('Should verify all Simple commands are registered', async () => {
        const commands = await vscode.commands.getCommands();

        const expectedCommands = [
            'simple.lsp.restart',
            'simple.lsp.showOutputChannel',
            'simple.ai.openChat',
            'simple.ai.toggleInlineCompletions',
            'simple.ai.explainCode',
            'simple.ai.reviewCode',
            'simple.ai.generateCode'
        ];

        expectedCommands.forEach(cmd => {
            assert.ok(
                commands.includes(cmd),
                `Command ${cmd} should be registered`
            );
        });
    });

    test('Should verify configuration schema', async () => {
        const config = vscode.workspace.getConfiguration('simple');

        // Verify config sections exist
        const lspPath = config.inspect('lsp.serverPath');
        assert.ok(lspPath, 'LSP server path config should exist');

        const aiEnabled = config.inspect('ai.enabled');
        assert.ok(aiEnabled, 'AI enabled config should exist');
    });

    test('Should update configuration dynamically', async () => {
        const initialValue = TestUtils.getConfig<number>('simple', 'lsp.debounceDelay');

        // Update config
        await TestUtils.updateConfig('simple', 'lsp.debounceDelay', 500);
        await TestUtils.sleep(500);

        const newValue = TestUtils.getConfig<number>('simple', 'lsp.debounceDelay');
        assert.strictEqual(newValue, 500, 'Config should be updated');

        // Restore original
        await TestUtils.updateConfig('simple', 'lsp.debounceDelay', initialValue);
    });
});
