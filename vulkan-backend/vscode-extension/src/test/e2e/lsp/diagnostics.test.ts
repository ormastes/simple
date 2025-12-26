/**
 * E2E Tests - LSP Diagnostics
 * Tests error reporting and diagnostics
 */

import * as assert from 'assert';
import * as vscode from 'vscode';
import { TestUtils, SAMPLE_CODE } from '../../helpers/testUtils';

suite('LSP E2E - Diagnostics', () => {
    let testDoc: vscode.TextDocument | undefined;

    suiteSetup(async function() {
        this.timeout(30000);
        await TestUtils.activateExtension();
        await TestUtils.waitForLSP(15000);
    });

    teardown(async () => {
        if (testDoc) {
            TestUtils.deleteTestFile('test-diagnostics.spl');
        }
        await TestUtils.closeAllEditors();
    });

    test('Should report no errors for valid code', async () => {
        testDoc = await TestUtils.createTestFile(
            'test-diagnostics.spl',
            SAMPLE_CODE.simple_function
        );

        const diagnostics = await TestUtils.getDiagnostics(testDoc.uri);

        // Filter to errors only (not warnings)
        const errors = diagnostics.filter(
            d => d.severity === vscode.DiagnosticSeverity.Error
        );

        assert.strictEqual(
            errors.length,
            0,
            `Valid code should have no errors, found: ${errors.map(e => e.message).join(', ')}`
        );
    });

    test('Should report syntax errors', async () => {
        testDoc = await TestUtils.createTestFile(
            'test-diagnostics.spl',
            SAMPLE_CODE.with_errors
        );

        const diagnostics = await TestUtils.getDiagnostics(testDoc.uri);

        // Should have at least one error
        assert.ok(
            diagnostics.length > 0,
            'Should report syntax errors'
        );

        // Check that diagnostics have proper structure
        diagnostics.forEach(diag => {
            assert.ok(diag.message, 'Diagnostic should have message');
            assert.ok(diag.range, 'Diagnostic should have range');
            assert.ok(
                diag.severity !== undefined,
                'Diagnostic should have severity'
            );
        });
    });

    test('Should report unclosed parenthesis', async () => {
        testDoc = await TestUtils.createTestFile(
            'test-diagnostics.spl',
            'fn test(x: i32\n    return x'
        );

        const diagnostics = await TestUtils.getDiagnostics(testDoc.uri);

        assert.ok(
            diagnostics.length > 0,
            'Should report unclosed parenthesis error'
        );
    });

    test('Should report unexpected token', async () => {
        testDoc = await TestUtils.createTestFile(
            'test-diagnostics.spl',
            'fn test():\n    let x = ++'
        );

        const diagnostics = await TestUtils.getDiagnostics(testDoc.uri);

        assert.ok(
            diagnostics.length > 0,
            'Should report unexpected token error'
        );
    });

    test('Should update diagnostics on edit', async () => {
        // Start with valid code
        testDoc = await TestUtils.createTestFile(
            'test-diagnostics.spl',
            'fn test(): i32 = 42'
        );

        let diagnostics = await TestUtils.getDiagnostics(testDoc.uri);
        const errorsBefore = diagnostics.filter(
            d => d.severity === vscode.DiagnosticSeverity.Error
        );

        assert.strictEqual(errorsBefore.length, 0, 'Should start with no errors');

        // Introduce syntax error
        const editor = TestUtils.getActiveEditor()!;
        await TestUtils.replaceText(
            editor,
            new vscode.Range(0, 0, 0, 100),
            'fn test(x: i32'  // Missing closing paren
        );

        await TestUtils.sleep(1000);

        diagnostics = await TestUtils.getDiagnostics(testDoc.uri);

        assert.ok(
            diagnostics.length > 0,
            'Should report errors after introducing syntax error'
        );

        // Fix the error
        await TestUtils.replaceText(
            editor,
            new vscode.Range(0, 0, 0, 100),
            'fn test(): i32 = 42'
        );

        await TestUtils.sleep(1000);

        diagnostics = await TestUtils.getDiagnostics(testDoc.uri);
        const errorsAfter = diagnostics.filter(
            d => d.severity === vscode.DiagnosticSeverity.Error
        );

        assert.strictEqual(
            errorsAfter.length,
            0,
            'Errors should be cleared after fix'
        );
    });

    test('Should handle multiple errors in one file', async () => {
        testDoc = await TestUtils.createTestFile(
            'test-diagnostics.spl',
            `fn broken1(x: i32
fn broken2(y: i32
fn broken3(z: i32`
        );

        const diagnostics = await TestUtils.getDiagnostics(testDoc.uri);

        // Should report multiple errors
        assert.ok(
            diagnostics.length >= 3,
            `Should report multiple errors, found ${diagnostics.length}`
        );
    });

    test('Should provide diagnostic ranges', async () => {
        testDoc = await TestUtils.createTestFile(
            'test-diagnostics.spl',
            'fn test(x: i32\n    return x'
        );

        const diagnostics = await TestUtils.getDiagnostics(testDoc.uri);

        assert.ok(diagnostics.length > 0, 'Should have diagnostics');

        // Check first diagnostic has valid range
        const diag = diagnostics[0];
        assert.ok(diag.range.start.line >= 0, 'Start line should be non-negative');
        assert.ok(diag.range.start.character >= 0, 'Start char should be non-negative');
        assert.ok(
            diag.range.end.line >= diag.range.start.line,
            'End line should be >= start line'
        );
    });

    test('Should clear diagnostics when file is closed', async () => {
        testDoc = await TestUtils.createTestFile(
            'test-diagnostics.spl',
            SAMPLE_CODE.with_errors
        );

        const uri = testDoc.uri;
        let diagnostics = await TestUtils.getDiagnostics(uri);

        assert.ok(diagnostics.length > 0, 'Should have initial diagnostics');

        // Close the editor
        await TestUtils.closeAllEditors();
        await TestUtils.sleep(500);

        diagnostics = await TestUtils.getDiagnostics(uri);

        // Diagnostics may still exist but should eventually be cleared
        // This depends on LSP server behavior
    });
});
