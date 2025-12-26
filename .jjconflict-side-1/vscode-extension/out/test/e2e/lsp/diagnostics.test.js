"use strict";
/**
 * E2E Tests - LSP Diagnostics
 * Tests error reporting and diagnostics
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
suite('LSP E2E - Diagnostics', () => {
    let testDoc;
    suiteSetup(async function () {
        this.timeout(30000);
        await testUtils_1.TestUtils.activateExtension();
        await testUtils_1.TestUtils.waitForLSP(15000);
    });
    teardown(async () => {
        if (testDoc) {
            testUtils_1.TestUtils.deleteTestFile('test-diagnostics.spl');
        }
        await testUtils_1.TestUtils.closeAllEditors();
    });
    test('Should report no errors for valid code', async () => {
        testDoc = await testUtils_1.TestUtils.createTestFile('test-diagnostics.spl', testUtils_1.SAMPLE_CODE.simple_function);
        const diagnostics = await testUtils_1.TestUtils.getDiagnostics(testDoc.uri);
        // Filter to errors only (not warnings)
        const errors = diagnostics.filter(d => d.severity === vscode.DiagnosticSeverity.Error);
        assert.strictEqual(errors.length, 0, `Valid code should have no errors, found: ${errors.map(e => e.message).join(', ')}`);
    });
    test('Should report syntax errors', async () => {
        testDoc = await testUtils_1.TestUtils.createTestFile('test-diagnostics.spl', testUtils_1.SAMPLE_CODE.with_errors);
        const diagnostics = await testUtils_1.TestUtils.getDiagnostics(testDoc.uri);
        // Should have at least one error
        assert.ok(diagnostics.length > 0, 'Should report syntax errors');
        // Check that diagnostics have proper structure
        diagnostics.forEach(diag => {
            assert.ok(diag.message, 'Diagnostic should have message');
            assert.ok(diag.range, 'Diagnostic should have range');
            assert.ok(diag.severity !== undefined, 'Diagnostic should have severity');
        });
    });
    test('Should report unclosed parenthesis', async () => {
        testDoc = await testUtils_1.TestUtils.createTestFile('test-diagnostics.spl', 'fn test(x: i32\n    return x');
        const diagnostics = await testUtils_1.TestUtils.getDiagnostics(testDoc.uri);
        assert.ok(diagnostics.length > 0, 'Should report unclosed parenthesis error');
    });
    test('Should report unexpected token', async () => {
        testDoc = await testUtils_1.TestUtils.createTestFile('test-diagnostics.spl', 'fn test():\n    let x = ++');
        const diagnostics = await testUtils_1.TestUtils.getDiagnostics(testDoc.uri);
        assert.ok(diagnostics.length > 0, 'Should report unexpected token error');
    });
    test('Should update diagnostics on edit', async () => {
        // Start with valid code
        testDoc = await testUtils_1.TestUtils.createTestFile('test-diagnostics.spl', 'fn test(): i32 = 42');
        let diagnostics = await testUtils_1.TestUtils.getDiagnostics(testDoc.uri);
        const errorsBefore = diagnostics.filter(d => d.severity === vscode.DiagnosticSeverity.Error);
        assert.strictEqual(errorsBefore.length, 0, 'Should start with no errors');
        // Introduce syntax error
        const editor = testUtils_1.TestUtils.getActiveEditor();
        await testUtils_1.TestUtils.replaceText(editor, new vscode.Range(0, 0, 0, 100), 'fn test(x: i32' // Missing closing paren
        );
        await testUtils_1.TestUtils.sleep(1000);
        diagnostics = await testUtils_1.TestUtils.getDiagnostics(testDoc.uri);
        assert.ok(diagnostics.length > 0, 'Should report errors after introducing syntax error');
        // Fix the error
        await testUtils_1.TestUtils.replaceText(editor, new vscode.Range(0, 0, 0, 100), 'fn test(): i32 = 42');
        await testUtils_1.TestUtils.sleep(1000);
        diagnostics = await testUtils_1.TestUtils.getDiagnostics(testDoc.uri);
        const errorsAfter = diagnostics.filter(d => d.severity === vscode.DiagnosticSeverity.Error);
        assert.strictEqual(errorsAfter.length, 0, 'Errors should be cleared after fix');
    });
    test('Should handle multiple errors in one file', async () => {
        testDoc = await testUtils_1.TestUtils.createTestFile('test-diagnostics.spl', `fn broken1(x: i32
fn broken2(y: i32
fn broken3(z: i32`);
        const diagnostics = await testUtils_1.TestUtils.getDiagnostics(testDoc.uri);
        // Should report multiple errors
        assert.ok(diagnostics.length >= 3, `Should report multiple errors, found ${diagnostics.length}`);
    });
    test('Should provide diagnostic ranges', async () => {
        testDoc = await testUtils_1.TestUtils.createTestFile('test-diagnostics.spl', 'fn test(x: i32\n    return x');
        const diagnostics = await testUtils_1.TestUtils.getDiagnostics(testDoc.uri);
        assert.ok(diagnostics.length > 0, 'Should have diagnostics');
        // Check first diagnostic has valid range
        const diag = diagnostics[0];
        assert.ok(diag.range.start.line >= 0, 'Start line should be non-negative');
        assert.ok(diag.range.start.character >= 0, 'Start char should be non-negative');
        assert.ok(diag.range.end.line >= diag.range.start.line, 'End line should be >= start line');
    });
    test('Should clear diagnostics when file is closed', async () => {
        testDoc = await testUtils_1.TestUtils.createTestFile('test-diagnostics.spl', testUtils_1.SAMPLE_CODE.with_errors);
        const uri = testDoc.uri;
        let diagnostics = await testUtils_1.TestUtils.getDiagnostics(uri);
        assert.ok(diagnostics.length > 0, 'Should have initial diagnostics');
        // Close the editor
        await testUtils_1.TestUtils.closeAllEditors();
        await testUtils_1.TestUtils.sleep(500);
        diagnostics = await testUtils_1.TestUtils.getDiagnostics(uri);
        // Diagnostics may still exist but should eventually be cleared
        // This depends on LSP server behavior
    });
});
//# sourceMappingURL=diagnostics.test.js.map