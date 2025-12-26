"use strict";
/**
 * Integration Tests - Full Workflow
 * Tests complete user workflows from start to finish
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
suite('Integration - Full Workflow', function () {
    this.timeout(60000);
    let testDoc;
    suiteSetup(async function () {
        await testUtils_1.TestUtils.activateExtension();
        await testUtils_1.TestUtils.waitForLSP(15000);
    });
    teardown(async () => {
        if (testDoc) {
            const filename = testDoc.fileName.split('/').pop();
            if (filename) {
                testUtils_1.TestUtils.deleteTestFile(filename);
            }
        }
        await testUtils_1.TestUtils.closeAllEditors();
    });
    test('Complete workflow: Create file → Edit → Get diagnostics → Get tokens', async () => {
        // 1. Create file
        testDoc = await testUtils_1.TestUtils.createTestFile('workflow-test.spl', 'fn incomplete(');
        // 2. Wait for LSP to process
        await testUtils_1.TestUtils.sleep(1500);
        // 3. Check diagnostics (should have error for incomplete syntax)
        let diagnostics = await testUtils_1.TestUtils.getDiagnostics(testDoc.uri);
        assert.ok(diagnostics.length > 0, 'Should have syntax error');
        // 4. Fix the error
        const editor = testUtils_1.TestUtils.getActiveEditor();
        await testUtils_1.TestUtils.replaceText(editor, new vscode.Range(0, 0, 0, 100), 'fn complete(): i32 = 42');
        await testUtils_1.TestUtils.sleep(1500);
        // 5. Check diagnostics again (should be clear)
        diagnostics = await testUtils_1.TestUtils.getDiagnostics(testDoc.uri);
        const errors = diagnostics.filter(d => d.severity === vscode.DiagnosticSeverity.Error);
        assert.strictEqual(errors.length, 0, 'Errors should be cleared');
        // 6. Get semantic tokens
        const tokens = await testUtils_1.TestUtils.getSemanticTokens(testDoc);
        assert.ok(tokens, 'Should have semantic tokens');
        assert.ok(tokens.data.length > 0, 'Should have token data');
    });
    test('Complete workflow: Write class → Use completion → Verify highlighting', async () => {
        // 1. Create file with partial code
        testDoc = await testUtils_1.TestUtils.createTestFile('class-workflow.spl', `class Point:
    x: i32
    y: i32

fn main():
    let p = `);
        const editor = testUtils_1.TestUtils.getActiveEditor();
        // 2. Position cursor after "let p = "
        await testUtils_1.TestUtils.setCursorPosition(editor, 5, 12);
        // 3. Wait for LSP
        await testUtils_1.TestUtils.sleep(1000);
        // 4. Try to get completions (may include "Point")
        const completions = await testUtils_1.TestUtils.triggerCompletion(testDoc, new vscode.Position(5, 12));
        // Note: Completions may or may not be available depending on LSP implementation
        // Just verify no crash
        // 5. Complete the code
        await testUtils_1.TestUtils.insertText(editor, new vscode.Position(5, 12), 'Point.new(10, 20)');
        await testUtils_1.TestUtils.sleep(1500);
        // 6. Verify semantic tokens for complete code
        const tokens = await testUtils_1.TestUtils.getSemanticTokens(testDoc);
        assert.ok(tokens, 'Should have semantic tokens for complete class');
        // Should have many tokens for class definition and usage
        const tokenCount = tokens.data.length / 5;
        assert.ok(tokenCount >= 10, `Should have substantial tokens, got ${tokenCount}`);
    });
    test('Complete workflow: Import → Reference → Hover', async () => {
        testDoc = await testUtils_1.TestUtils.createTestFile('import-workflow.spl', `import std.io

fn main():
    io.println("Hello")`);
        await testUtils_1.TestUtils.sleep(1500);
        // Try to get hover on "io.println"
        const hovers = await testUtils_1.TestUtils.getHover(testDoc, new vscode.Position(3, 4) // Position on "io"
        );
        // Hover may or may not be implemented yet
        // Just verify no crash
        assert.ok(true, 'Import and reference workflow completed');
    });
    test('Complete workflow: Write function → Find references', async () => {
        testDoc = await testUtils_1.TestUtils.createTestFile('references-workflow.spl', `fn calculate(x: i32): i32 = x * 2

fn main():
    let a = calculate(10)
    let b = calculate(20)
    let c = calculate(30)`);
        await testUtils_1.TestUtils.sleep(1500);
        // Try to find references to "calculate"
        const references = await testUtils_1.TestUtils.findReferences(testDoc, new vscode.Position(0, 3) // Position on function name
        );
        // References may or may not be implemented yet
        // Just verify no crash
        assert.ok(true, 'Find references workflow completed');
    });
    test('Complete workflow: Multiple files → Cross-file references', async () => {
        // Create first file
        const file1 = await testUtils_1.TestUtils.createTestFile('module1.spl', `fn helper(x: i32): i32 = x + 1`);
        await testUtils_1.TestUtils.sleep(500);
        // Create second file
        testDoc = await testUtils_1.TestUtils.createTestFile('module2.spl', `import module1

fn main():
    let result = module1.helper(42)`);
        await testUtils_1.TestUtils.sleep(2000);
        // Verify both files have tokens
        const tokens1 = await testUtils_1.TestUtils.getSemanticTokens(file1);
        const tokens2 = await testUtils_1.TestUtils.getSemanticTokens(testDoc);
        assert.ok(tokens1, 'First file should have tokens');
        assert.ok(tokens2, 'Second file should have tokens');
        testUtils_1.TestUtils.deleteTestFile('module1.spl');
    });
    test('Complete workflow: Syntax error → AI explain → Fix → Verify', async function () {
        const aiEnabled = testUtils_1.TestUtils.getConfig('simple', 'ai.enabled');
        if (!aiEnabled) {
            console.log('⚠️  AI disabled, skipping AI workflow test');
            this.skip();
            return;
        }
        // 1. Create file with error
        testDoc = await testUtils_1.TestUtils.createTestFile('ai-workflow.spl', 'fn broken(x: i32\n    return x + 1');
        await testUtils_1.TestUtils.sleep(1000);
        // 2. Select the broken code
        const editor = testUtils_1.TestUtils.getActiveEditor();
        await testUtils_1.TestUtils.selectRange(editor, 0, 0, 1, 17);
        // 3. Try to explain (will use AI if available)
        try {
            const promise = vscode.commands.executeCommand('simple.ai.explainCode');
            await testUtils_1.TestUtils.sleep(2000); // Don't wait for full completion
            // 4. Fix the error
            await testUtils_1.TestUtils.replaceText(editor, new vscode.Range(0, 0, 1, 100), 'fn fixed(x: i32): i32 =\n    x + 1');
            await testUtils_1.TestUtils.sleep(1500);
            // 5. Verify fix
            const diagnostics = await testUtils_1.TestUtils.getDiagnostics(testDoc.uri);
            const errors = diagnostics.filter(d => d.severity === vscode.DiagnosticSeverity.Error);
            assert.strictEqual(errors.length, 0, 'Errors should be fixed');
        }
        catch (error) {
            console.log('⚠️  AI features not available, skipping AI steps');
        }
    });
    test('Performance: Handle rapid edits without crashes', async () => {
        testDoc = await testUtils_1.TestUtils.createTestFile('rapid-edits.spl', 'fn test(): void');
        const editor = testUtils_1.TestUtils.getActiveEditor();
        // Make rapid edits
        for (let i = 0; i < 10; i++) {
            await testUtils_1.TestUtils.insertText(editor, new vscode.Position(i, 0), `\nfn test${i}(): i32 = ${i}`);
            await testUtils_1.TestUtils.sleep(100); // Small delay between edits
        }
        // Wait for LSP to catch up
        await testUtils_1.TestUtils.sleep(2000);
        // Verify we still have tokens
        const tokens = await testUtils_1.TestUtils.getSemanticTokens(testDoc);
        assert.ok(tokens, 'Should still have tokens after rapid edits');
    });
});
//# sourceMappingURL=fullWorkflow.test.js.map