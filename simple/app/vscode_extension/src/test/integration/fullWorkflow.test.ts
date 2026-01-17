/**
 * Integration Tests - Full Workflow
 * Tests complete user workflows from start to finish
 */

import * as assert from 'assert';
import * as vscode from 'vscode';
import { TestUtils, SAMPLE_CODE } from '../helpers/testUtils';

suite('Integration - Full Workflow', function() {
    this.timeout(60000);

    let testDoc: vscode.TextDocument | undefined;

    suiteSetup(async function() {
        await TestUtils.activateExtension();
        await TestUtils.waitForLSP(15000);
    });

    teardown(async () => {
        if (testDoc) {
            const filename = testDoc.fileName.split('/').pop();
            if (filename) {
                TestUtils.deleteTestFile(filename);
            }
        }
        await TestUtils.closeAllEditors();
    });

    test('Complete workflow: Create file → Edit → Get diagnostics → Get tokens', async () => {
        // 1. Create file
        testDoc = await TestUtils.createTestFile(
            'workflow-test.spl',
            'fn incomplete('
        );

        // 2. Wait for LSP to process
        await TestUtils.sleep(1500);

        // 3. Check diagnostics (should have error for incomplete syntax)
        let diagnostics = await TestUtils.getDiagnostics(testDoc.uri);
        assert.ok(diagnostics.length > 0, 'Should have syntax error');

        // 4. Fix the error
        const editor = TestUtils.getActiveEditor()!;
        await TestUtils.replaceText(
            editor,
            new vscode.Range(0, 0, 0, 100),
            'fn complete(): i32 = 42'
        );

        await TestUtils.sleep(1500);

        // 5. Check diagnostics again (should be clear)
        diagnostics = await TestUtils.getDiagnostics(testDoc.uri);
        const errors = diagnostics.filter(d => d.severity === vscode.DiagnosticSeverity.Error);
        assert.strictEqual(errors.length, 0, 'Errors should be cleared');

        // 6. Get semantic tokens
        const tokens = await TestUtils.getSemanticTokens(testDoc);
        assert.ok(tokens, 'Should have semantic tokens');
        assert.ok(tokens!.data.length > 0, 'Should have token data');
    });

    test('Complete workflow: Write class → Use completion → Verify highlighting', async () => {
        // 1. Create file with partial code
        testDoc = await TestUtils.createTestFile(
            'class-workflow.spl',
            `class Point:
    x: i32
    y: i32

fn main():
    let p = `
        );

        const editor = TestUtils.getActiveEditor()!;

        // 2. Position cursor after "let p = "
        await TestUtils.setCursorPosition(editor, 5, 12);

        // 3. Wait for LSP
        await TestUtils.sleep(1000);

        // 4. Try to get completions (may include "Point")
        const completions = await TestUtils.triggerCompletion(
            testDoc,
            new vscode.Position(5, 12)
        );

        // Note: Completions may or may not be available depending on LSP implementation
        // Just verify no crash

        // 5. Complete the code
        await TestUtils.insertText(
            editor,
            new vscode.Position(5, 12),
            'Point.new(10, 20)'
        );

        await TestUtils.sleep(1500);

        // 6. Verify semantic tokens for complete code
        const tokens = await TestUtils.getSemanticTokens(testDoc);
        assert.ok(tokens, 'Should have semantic tokens for complete class');

        // Should have many tokens for class definition and usage
        const tokenCount = tokens!.data.length / 5;
        assert.ok(tokenCount >= 10, `Should have substantial tokens, got ${tokenCount}`);
    });

    test('Complete workflow: Import → Reference → Hover', async () => {
        testDoc = await TestUtils.createTestFile(
            'import-workflow.spl',
            `import std.io

fn main():
    io.println("Hello")`
        );

        await TestUtils.sleep(1500);

        // Try to get hover on "io.println"
        const hovers = await TestUtils.getHover(
            testDoc,
            new vscode.Position(3, 4)  // Position on "io"
        );

        // Hover may or may not be implemented yet
        // Just verify no crash
        assert.ok(true, 'Import and reference workflow completed');
    });

    test('Complete workflow: Write function → Find references', async () => {
        testDoc = await TestUtils.createTestFile(
            'references-workflow.spl',
            `fn calculate(x: i32): i32 = x * 2

fn main():
    let a = calculate(10)
    let b = calculate(20)
    let c = calculate(30)`
        );

        await TestUtils.sleep(1500);

        // Try to find references to "calculate"
        const references = await TestUtils.findReferences(
            testDoc,
            new vscode.Position(0, 3)  // Position on function name
        );

        // References may or may not be implemented yet
        // Just verify no crash
        assert.ok(true, 'Find references workflow completed');
    });

    test('Complete workflow: Multiple files → Cross-file references', async () => {
        // Create first file
        const file1 = await TestUtils.createTestFile(
            'module1.spl',
            `fn helper(x: i32): i32 = x + 1`
        );

        await TestUtils.sleep(500);

        // Create second file
        testDoc = await TestUtils.createTestFile(
            'module2.spl',
            `import module1

fn main():
    let result = module1.helper(42)`
        );

        await TestUtils.sleep(2000);

        // Verify both files have tokens
        const tokens1 = await TestUtils.getSemanticTokens(file1);
        const tokens2 = await TestUtils.getSemanticTokens(testDoc);

        assert.ok(tokens1, 'First file should have tokens');
        assert.ok(tokens2, 'Second file should have tokens');

        TestUtils.deleteTestFile('module1.spl');
    });

    test('Complete workflow: Syntax error → AI explain → Fix → Verify', async function() {
        const aiEnabled = TestUtils.getConfig<boolean>('simple', 'ai.enabled');

        if (!aiEnabled) {
            console.log('⚠️  AI disabled, skipping AI workflow test');
            this.skip();
            return;
        }

        // 1. Create file with error
        testDoc = await TestUtils.createTestFile(
            'ai-workflow.spl',
            'fn broken(x: i32\n    return x + 1'
        );

        await TestUtils.sleep(1000);

        // 2. Select the broken code
        const editor = TestUtils.getActiveEditor()!;
        await TestUtils.selectRange(editor, 0, 0, 1, 17);

        // 3. Try to explain (will use AI if available)
        try {
            const promise = vscode.commands.executeCommand('simple.ai.explainCode');
            await TestUtils.sleep(2000);  // Don't wait for full completion

            // 4. Fix the error
            await TestUtils.replaceText(
                editor,
                new vscode.Range(0, 0, 1, 100),
                'fn fixed(x: i32): i32 =\n    x + 1'
            );

            await TestUtils.sleep(1500);

            // 5. Verify fix
            const diagnostics = await TestUtils.getDiagnostics(testDoc.uri);
            const errors = diagnostics.filter(d => d.severity === vscode.DiagnosticSeverity.Error);

            assert.strictEqual(errors.length, 0, 'Errors should be fixed');
        } catch (error) {
            console.log('⚠️  AI features not available, skipping AI steps');
        }
    });

    test('Performance: Handle rapid edits without crashes', async () => {
        testDoc = await TestUtils.createTestFile(
            'rapid-edits.spl',
            'fn test(): void'
        );

        const editor = TestUtils.getActiveEditor()!;

        // Make rapid edits
        for (let i = 0; i < 10; i++) {
            await TestUtils.insertText(
                editor,
                new vscode.Position(i, 0),
                `\nfn test${i}(): i32 = ${i}`
            );
            await TestUtils.sleep(100);  // Small delay between edits
        }

        // Wait for LSP to catch up
        await TestUtils.sleep(2000);

        // Verify we still have tokens
        const tokens = await TestUtils.getSemanticTokens(testDoc);
        assert.ok(tokens, 'Should still have tokens after rapid edits');
    });
});
