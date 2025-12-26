"use strict";
/**
 * E2E Tests - LSP Semantic Tokens
 * Tests Tree-sitter powered semantic highlighting
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
const testUtils_1 = require("../../helpers/testUtils");
suite('LSP E2E - Semantic Tokens', () => {
    let testDoc;
    suiteSetup(async function () {
        this.timeout(30000);
        // Ensure extension is activated
        await testUtils_1.TestUtils.activateExtension();
        // Wait for LSP server to start
        await testUtils_1.TestUtils.waitForLSP(15000);
    });
    teardown(async () => {
        if (testDoc) {
            testUtils_1.TestUtils.deleteTestFile('test-semantic.spl');
        }
        await testUtils_1.TestUtils.closeAllEditors();
    });
    test('Should provide semantic tokens for simple function', async () => {
        testDoc = await testUtils_1.TestUtils.createTestFile('test-semantic.spl', testUtils_1.SAMPLE_CODE.simple_function);
        // Wait for semantic tokens
        await testUtils_1.TestUtils.sleep(2000);
        const tokens = await testUtils_1.TestUtils.getSemanticTokens(testDoc);
        assert.ok(tokens, 'Should return semantic tokens');
        assert.ok(tokens.data.length > 0, 'Should have token data');
        // Verify we have tokens (encoded as array of 5-tuples)
        assert.strictEqual(tokens.data.length % 5, 0, 'Token data should be divisible by 5');
        // Should have at least tokens for: fn, add, i32, x, y, main, let, result, print
        const tokenCount = tokens.data.length / 5;
        assert.ok(tokenCount >= 9, `Should have at least 9 tokens, got ${tokenCount}`);
    });
    test('Should provide semantic tokens for class definition', async () => {
        testDoc = await testUtils_1.TestUtils.createTestFile('test-semantic.spl', testUtils_1.SAMPLE_CODE.class_definition);
        await testUtils_1.TestUtils.sleep(2000);
        const tokens = await testUtils_1.TestUtils.getSemanticTokens(testDoc);
        assert.ok(tokens, 'Should return semantic tokens');
        assert.ok(tokens.data.length > 0, 'Should have token data');
        // Should have tokens for: class, Point, x, y, i32, fn, new, self, distance, f64, sqrt
        const tokenCount = tokens.data.length / 5;
        assert.ok(tokenCount >= 11, `Should have at least 11 tokens, got ${tokenCount}`);
    });
    test('Should update semantic tokens on edit', async () => {
        testDoc = await testUtils_1.TestUtils.createTestFile('test-semantic.spl', 'fn simple(): i32 = 42');
        await testUtils_1.TestUtils.sleep(1000);
        const tokensBefore = await testUtils_1.TestUtils.getSemanticTokens(testDoc);
        const countBefore = tokensBefore.data.length / 5;
        // Edit the document
        const editor = testUtils_1.TestUtils.getActiveEditor();
        await testUtils_1.TestUtils.insertText(editor, new vscode.Position(1, 0), '\nfn another(): i32 = 100\n');
        // Wait for incremental update
        await testUtils_1.TestUtils.sleep(1500);
        const tokensAfter = await testUtils_1.TestUtils.getSemanticTokens(testDoc);
        const countAfter = tokensAfter.data.length / 5;
        // Should have more tokens after adding a function
        assert.ok(countAfter > countBefore, `Token count should increase: ${countBefore} -> ${countAfter}`);
    });
    test('Should handle syntax errors gracefully', async () => {
        testDoc = await testUtils_1.TestUtils.createTestFile('test-semantic.spl', testUtils_1.SAMPLE_CODE.with_errors);
        await testUtils_1.TestUtils.sleep(2000);
        // Should still provide tokens even with errors
        const tokens = await testUtils_1.TestUtils.getSemanticTokens(testDoc);
        assert.ok(tokens, 'Should return tokens even with syntax errors');
        // May have fewer tokens due to errors, but should not crash
    });
    test('Should tokenize async functions', async () => {
        testDoc = await testUtils_1.TestUtils.createTestFile('test-semantic.spl', testUtils_1.SAMPLE_CODE.async_function);
        await testUtils_1.TestUtils.sleep(2000);
        const tokens = await testUtils_1.TestUtils.getSemanticTokens(testDoc);
        assert.ok(tokens, 'Should return semantic tokens');
        assert.ok(tokens.data.length > 0, 'Should have token data');
        // Should tokenize: async, fn, await, Result, String, etc.
        const tokenCount = tokens.data.length / 5;
        assert.ok(tokenCount >= 10, `Should have at least 10 tokens, got ${tokenCount}`);
    });
    test('Should tokenize import statements', async () => {
        testDoc = await testUtils_1.TestUtils.createTestFile('test-semantic.spl', testUtils_1.SAMPLE_CODE.imports);
        await testUtils_1.TestUtils.sleep(2000);
        const tokens = await testUtils_1.TestUtils.getSemanticTokens(testDoc);
        assert.ok(tokens, 'Should return semantic tokens');
        assert.ok(tokens.data.length > 0, 'Should have token data');
        // Should tokenize: import, std, io, collections, as, coll, from, math, sqrt, pow
        const tokenCount = tokens.data.length / 5;
        assert.ok(tokenCount >= 10, `Should have at least 10 tokens, got ${tokenCount}`);
    });
    test('Should provide consistent token encoding', async () => {
        testDoc = await testUtils_1.TestUtils.createTestFile('test-semantic.spl', 'fn test(): void');
        await testUtils_1.TestUtils.sleep(1000);
        const tokens1 = await testUtils_1.TestUtils.getSemanticTokens(testDoc);
        await testUtils_1.TestUtils.sleep(500);
        const tokens2 = await testUtils_1.TestUtils.getSemanticTokens(testDoc);
        // Same document should produce same tokens
        assert.deepStrictEqual(tokens1.data, tokens2.data, 'Token encoding should be consistent');
    });
    test('Should handle empty file', async () => {
        testDoc = await testUtils_1.TestUtils.createTestFile('test-semantic.spl', '');
        await testUtils_1.TestUtils.sleep(1000);
        const tokens = await testUtils_1.TestUtils.getSemanticTokens(testDoc);
        assert.ok(tokens, 'Should return tokens for empty file');
        assert.strictEqual(tokens.data.length, 0, 'Empty file should have no tokens');
    });
    test('Should tokenize fibonacci function', async () => {
        testDoc = await testUtils_1.TestUtils.createTestFile('test-semantic.spl', testUtils_1.SAMPLE_CODE.fibonacci);
        await testUtils_1.TestUtils.sleep(2000);
        const tokens = await testUtils_1.TestUtils.getSemanticTokens(testDoc);
        assert.ok(tokens, 'Should return semantic tokens');
        // Should have tokens for: fn, fibonacci, n, i32 (×3), if, -, else, +
        const tokenCount = tokens.data.length / 5;
        assert.ok(tokenCount >= 10, `Should have at least 10 tokens, got ${tokenCount}`);
    });
});
//# sourceMappingURL=semanticTokens.test.js.map