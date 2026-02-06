/**
 * E2E Tests - LSP Semantic Tokens
 * Tests Tree-sitter powered semantic highlighting
 */

import * as assert from 'assert';
import * as vscode from 'vscode';
import { TestUtils, SAMPLE_CODE } from '../../helpers/testUtils';

suite('LSP E2E - Semantic Tokens', () => {
    let testDoc: vscode.TextDocument | undefined;

    suiteSetup(async function() {
        this.timeout(30000);
        // Ensure extension is activated
        await TestUtils.activateExtension();
        // Wait for LSP server to start
        await TestUtils.waitForLSP(15000);
    });

    teardown(async () => {
        if (testDoc) {
            TestUtils.deleteTestFile('test-semantic.spl');
        }
        await TestUtils.closeAllEditors();
    });

    test('Should provide semantic tokens for simple function', async () => {
        testDoc = await TestUtils.createTestFile(
            'test-semantic.spl',
            SAMPLE_CODE.simple_function
        );

        // Wait for semantic tokens
        await TestUtils.sleep(2000);

        const tokens = await TestUtils.getSemanticTokens(testDoc);

        assert.ok(tokens, 'Should return semantic tokens');
        assert.ok(tokens!.data.length > 0, 'Should have token data');

        // Verify we have tokens (encoded as array of 5-tuples)
        assert.strictEqual(
            tokens!.data.length % 5,
            0,
            'Token data should be divisible by 5'
        );

        // Should have at least tokens for: fn, add, i32, x, y, main, let, result, print
        const tokenCount = tokens!.data.length / 5;
        assert.ok(tokenCount >= 9, `Should have at least 9 tokens, got ${tokenCount}`);
    });

    test('Should provide semantic tokens for class definition', async () => {
        testDoc = await TestUtils.createTestFile(
            'test-semantic.spl',
            SAMPLE_CODE.class_definition
        );

        await TestUtils.sleep(2000);

        const tokens = await TestUtils.getSemanticTokens(testDoc);

        assert.ok(tokens, 'Should return semantic tokens');
        assert.ok(tokens!.data.length > 0, 'Should have token data');

        // Should have tokens for: class, Point, x, y, i32, fn, new, self, distance, f64, sqrt
        const tokenCount = tokens!.data.length / 5;
        assert.ok(tokenCount >= 11, `Should have at least 11 tokens, got ${tokenCount}`);
    });

    test('Should update semantic tokens on edit', async () => {
        testDoc = await TestUtils.createTestFile(
            'test-semantic.spl',
            'fn simple(): i32 = 42'
        );

        await TestUtils.sleep(1000);

        const tokensBefore = await TestUtils.getSemanticTokens(testDoc);
        const countBefore = tokensBefore!.data.length / 5;

        // Edit the document
        const editor = TestUtils.getActiveEditor()!;
        await TestUtils.insertText(
            editor,
            new vscode.Position(1, 0),
            '\nfn another(): i32 = 100\n'
        );

        // Wait for incremental update
        await TestUtils.sleep(1500);

        const tokensAfter = await TestUtils.getSemanticTokens(testDoc);
        const countAfter = tokensAfter!.data.length / 5;

        // Should have more tokens after adding a function
        assert.ok(
            countAfter > countBefore,
            `Token count should increase: ${countBefore} -> ${countAfter}`
        );
    });

    test('Should handle syntax errors gracefully', async () => {
        testDoc = await TestUtils.createTestFile(
            'test-semantic.spl',
            SAMPLE_CODE.with_errors
        );

        await TestUtils.sleep(2000);

        // Should still provide tokens even with errors
        const tokens = await TestUtils.getSemanticTokens(testDoc);

        assert.ok(tokens, 'Should return tokens even with syntax errors');
        // May have fewer tokens due to errors, but should not crash
    });

    test('Should tokenize async functions', async () => {
        testDoc = await TestUtils.createTestFile(
            'test-semantic.spl',
            SAMPLE_CODE.async_function
        );

        await TestUtils.sleep(2000);

        const tokens = await TestUtils.getSemanticTokens(testDoc);

        assert.ok(tokens, 'Should return semantic tokens');
        assert.ok(tokens!.data.length > 0, 'Should have token data');

        // Should tokenize: async, fn, await, Result, String, etc.
        const tokenCount = tokens!.data.length / 5;
        assert.ok(tokenCount >= 10, `Should have at least 10 tokens, got ${tokenCount}`);
    });

    test('Should tokenize import statements', async () => {
        testDoc = await TestUtils.createTestFile(
            'test-semantic.spl',
            SAMPLE_CODE.imports
        );

        await TestUtils.sleep(2000);

        const tokens = await TestUtils.getSemanticTokens(testDoc);

        assert.ok(tokens, 'Should return semantic tokens');
        assert.ok(tokens!.data.length > 0, 'Should have token data');

        // Should tokenize: import, std, io, collections, as, coll, from, math, sqrt, pow
        const tokenCount = tokens!.data.length / 5;
        assert.ok(tokenCount >= 10, `Should have at least 10 tokens, got ${tokenCount}`);
    });

    test('Should provide consistent token encoding', async () => {
        testDoc = await TestUtils.createTestFile(
            'test-semantic.spl',
            'fn test(): void'
        );

        await TestUtils.sleep(1000);

        const tokens1 = await TestUtils.getSemanticTokens(testDoc);
        await TestUtils.sleep(500);
        const tokens2 = await TestUtils.getSemanticTokens(testDoc);

        // Same document should produce same tokens
        assert.deepStrictEqual(
            tokens1!.data,
            tokens2!.data,
            'Token encoding should be consistent'
        );
    });

    test('Should handle empty file', async () => {
        testDoc = await TestUtils.createTestFile('test-semantic.spl', '');

        await TestUtils.sleep(1000);

        const tokens = await TestUtils.getSemanticTokens(testDoc);

        assert.ok(tokens, 'Should return tokens for empty file');
        assert.strictEqual(tokens!.data.length, 0, 'Empty file should have no tokens');
    });

    test('Should tokenize fibonacci function', async () => {
        testDoc = await TestUtils.createTestFile(
            'test-semantic.spl',
            SAMPLE_CODE.fibonacci
        );

        await TestUtils.sleep(2000);

        const tokens = await TestUtils.getSemanticTokens(testDoc);

        assert.ok(tokens, 'Should return semantic tokens');

        // Should have tokens for: fn, fibonacci, n, i32 (×3), if, -, else, +
        const tokenCount = tokens!.data.length / 5;
        assert.ok(tokenCount >= 10, `Should have at least 10 tokens, got ${tokenCount}`);
    });
});
