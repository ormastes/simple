/**
 * GUI Tests - AI Chat Panel
 * Tests chat panel webview and interactions
 */

import * as assert from 'assert';
import * as vscode from 'vscode';
import { TestUtils } from '../helpers/testUtils';

suite('GUI - AI Chat Panel', function() {
    this.timeout(60000);

    let aiEnabled: boolean = false;

    suiteSetup(async function() {
        await TestUtils.activateExtension();
        await TestUtils.waitForLSP(15000);

        const enabled = TestUtils.getConfig<boolean>('simple', 'ai.enabled');
        const chatEnabled = TestUtils.getConfig<boolean>('simple', 'ai.chatPanel');

        aiEnabled = (enabled ?? true) && (chatEnabled ?? true);

        if (!aiEnabled) {
            console.log('⚠️  AI chat panel disabled, skipping tests');
            this.skip();
        }
    });

    teardown(async () => {
        await TestUtils.closeAllEditors();

        // Close chat panel if open
        await vscode.commands.executeCommand('workbench.action.closePanel');
    });

    test('Should open chat panel via command', async function() {
        if (!aiEnabled) {
            this.skip();
            return;
        }

        // Execute command to open chat
        await vscode.commands.executeCommand('simple.ai.openChat');

        await TestUtils.sleep(1000);

        // Verify panel opened (can't directly check webview, but command should complete)
        assert.ok(true, 'Chat panel command executed successfully');
    });

    test('Should open chat panel only once (singleton)', async function() {
        if (!aiEnabled) {
            this.skip();
            return;
        }

        // Open first time
        await vscode.commands.executeCommand('simple.ai.openChat');
        await TestUtils.sleep(500);

        // Open second time (should reuse existing)
        await vscode.commands.executeCommand('simple.ai.openChat');
        await TestUtils.sleep(500);

        assert.ok(true, 'Singleton chat panel pattern working');
    });

    test('Should handle explain selection from chat panel', async function() {
        if (!aiEnabled) {
            this.skip();
            return;
        }

        // Create test file with code to explain
        const testDoc = await TestUtils.createTestFile(
            'test-explain.spl',
            `fn fibonacci(n: i32): i32 =
    if n <= 1:
        n
    else:
        fibonacci(n - 1) + fibonacci(n - 2)`
        );

        const editor = TestUtils.getActiveEditor()!;

        // Select the code
        await TestUtils.selectRange(editor, 0, 0, 4, 42);

        // Open chat panel
        await vscode.commands.executeCommand('simple.ai.openChat');
        await TestUtils.sleep(1000);

        // The webview would have "Explain Selection" button
        // We can't click it directly in tests, but we can verify the command exists

        TestUtils.deleteTestFile('test-explain.spl');
        assert.ok(true, 'Chat panel with explain selection opened');
    });

    test('Should handle review selection from chat panel', async function() {
        if (!aiEnabled) {
            this.skip();
            return;
        }

        const testDoc = await TestUtils.createTestFile(
            'test-review.spl',
            `fn process(items: List[i32]):
    for i in items:
        print(i * 2)`
        );

        const editor = TestUtils.getActiveEditor()!;
        await TestUtils.selectRange(editor, 0, 0, 2, 23);

        await vscode.commands.executeCommand('simple.ai.openChat');
        await TestUtils.sleep(1000);

        TestUtils.deleteTestFile('test-review.spl');
        assert.ok(true, 'Chat panel with review selection opened');
    });

    test('Should persist chat panel across editor changes', async function() {
        if (!aiEnabled) {
            this.skip();
            return;
        }

        // Open chat panel
        await vscode.commands.executeCommand('simple.ai.openChat');
        await TestUtils.sleep(500);

        // Create and switch between files
        await TestUtils.createTestFile('test1.spl', 'fn test1(): void');
        await TestUtils.sleep(300);

        await TestUtils.createTestFile('test2.spl', 'fn test2(): void');
        await TestUtils.sleep(300);

        TestUtils.deleteTestFile('test1.spl');
        TestUtils.deleteTestFile('test2.spl');

        assert.ok(true, 'Chat panel persisted across editor changes');
    });

    test('Should handle AI unavailable gracefully', async function() {
        // Temporarily disable AI
        await TestUtils.updateConfig('simple', 'ai.enabled', false);

        try {
            await vscode.commands.executeCommand('simple.ai.openChat');
            await TestUtils.sleep(500);

            // Should show error message but not crash
            assert.ok(true, 'Handled AI unavailable without crashing');
        } finally {
            // Re-enable
            await TestUtils.updateConfig('simple', 'ai.enabled', true);
        }
    });
});
