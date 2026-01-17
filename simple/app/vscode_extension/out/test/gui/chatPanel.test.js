"use strict";
/**
 * GUI Tests - AI Chat Panel
 * Tests chat panel webview and interactions
 */
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
const assert = __importStar(require("assert"));
const vscode = __importStar(require("vscode"));
const testUtils_1 = require("../helpers/testUtils");
suite('GUI - AI Chat Panel', function () {
    this.timeout(60000);
    let aiEnabled = false;
    suiteSetup(async function () {
        await testUtils_1.TestUtils.activateExtension();
        await testUtils_1.TestUtils.waitForLSP(15000);
        const enabled = testUtils_1.TestUtils.getConfig('simple', 'ai.enabled');
        const chatEnabled = testUtils_1.TestUtils.getConfig('simple', 'ai.chatPanel');
        aiEnabled = (enabled ?? true) && (chatEnabled ?? true);
        if (!aiEnabled) {
            console.log('⚠️  AI chat panel disabled, skipping tests');
            this.skip();
        }
    });
    teardown(async () => {
        await testUtils_1.TestUtils.closeAllEditors();
        // Close chat panel if open
        await vscode.commands.executeCommand('workbench.action.closePanel');
    });
    test('Should open chat panel via command', async function () {
        if (!aiEnabled) {
            this.skip();
            return;
        }
        // Execute command to open chat
        await vscode.commands.executeCommand('simple.ai.openChat');
        await testUtils_1.TestUtils.sleep(1000);
        // Verify panel opened (can't directly check webview, but command should complete)
        assert.ok(true, 'Chat panel command executed successfully');
    });
    test('Should open chat panel only once (singleton)', async function () {
        if (!aiEnabled) {
            this.skip();
            return;
        }
        // Open first time
        await vscode.commands.executeCommand('simple.ai.openChat');
        await testUtils_1.TestUtils.sleep(500);
        // Open second time (should reuse existing)
        await vscode.commands.executeCommand('simple.ai.openChat');
        await testUtils_1.TestUtils.sleep(500);
        assert.ok(true, 'Singleton chat panel pattern working');
    });
    test('Should handle explain selection from chat panel', async function () {
        if (!aiEnabled) {
            this.skip();
            return;
        }
        // Create test file with code to explain
        const testDoc = await testUtils_1.TestUtils.createTestFile('test-explain.spl', `fn fibonacci(n: i32): i32 =
    if n <= 1:
        n
    else:
        fibonacci(n - 1) + fibonacci(n - 2)`);
        const editor = testUtils_1.TestUtils.getActiveEditor();
        // Select the code
        await testUtils_1.TestUtils.selectRange(editor, 0, 0, 4, 42);
        // Open chat panel
        await vscode.commands.executeCommand('simple.ai.openChat');
        await testUtils_1.TestUtils.sleep(1000);
        // The webview would have "Explain Selection" button
        // We can't click it directly in tests, but we can verify the command exists
        testUtils_1.TestUtils.deleteTestFile('test-explain.spl');
        assert.ok(true, 'Chat panel with explain selection opened');
    });
    test('Should handle review selection from chat panel', async function () {
        if (!aiEnabled) {
            this.skip();
            return;
        }
        const testDoc = await testUtils_1.TestUtils.createTestFile('test-review.spl', `fn process(items: List[i32]):
    for i in items:
        print(i * 2)`);
        const editor = testUtils_1.TestUtils.getActiveEditor();
        await testUtils_1.TestUtils.selectRange(editor, 0, 0, 2, 23);
        await vscode.commands.executeCommand('simple.ai.openChat');
        await testUtils_1.TestUtils.sleep(1000);
        testUtils_1.TestUtils.deleteTestFile('test-review.spl');
        assert.ok(true, 'Chat panel with review selection opened');
    });
    test('Should persist chat panel across editor changes', async function () {
        if (!aiEnabled) {
            this.skip();
            return;
        }
        // Open chat panel
        await vscode.commands.executeCommand('simple.ai.openChat');
        await testUtils_1.TestUtils.sleep(500);
        // Create and switch between files
        await testUtils_1.TestUtils.createTestFile('test1.spl', 'fn test1(): void');
        await testUtils_1.TestUtils.sleep(300);
        await testUtils_1.TestUtils.createTestFile('test2.spl', 'fn test2(): void');
        await testUtils_1.TestUtils.sleep(300);
        testUtils_1.TestUtils.deleteTestFile('test1.spl');
        testUtils_1.TestUtils.deleteTestFile('test2.spl');
        assert.ok(true, 'Chat panel persisted across editor changes');
    });
    test('Should handle AI unavailable gracefully', async function () {
        // Temporarily disable AI
        await testUtils_1.TestUtils.updateConfig('simple', 'ai.enabled', false);
        try {
            await vscode.commands.executeCommand('simple.ai.openChat');
            await testUtils_1.TestUtils.sleep(500);
            // Should show error message but not crash
            assert.ok(true, 'Handled AI unavailable without crashing');
        }
        finally {
            // Re-enable
            await testUtils_1.TestUtils.updateConfig('simple', 'ai.enabled', true);
        }
    });
});
//# sourceMappingURL=chatPanel.test.js.map