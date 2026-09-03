import * as assert from 'assert';
import * as path from 'path';
import * as vscode from 'vscode';
import { analyzeDocument } from '../../analysis/simpleAnalysisIndex';
import { authoritativeLspReceipt, degradedLspReceipt } from '../../lsp/simpleLspCapabilityReceipt';
import { createSimpleLspDocumentSelector } from '../../services/simpleLspServerResolver';

suite('browser and WASM canonical parity', () => {
    test('uses one selector for file, untitled, and virtual workspaces', () => {
        assert.deepStrictEqual(createSimpleLspDocumentSelector(), [
            { scheme: 'file', language: 'simple' },
            { scheme: 'untitled', language: 'simple' },
            { scheme: 'vscode-vfs', language: 'simple' },
        ]);
    });

    test('labels fallback output as syntax-only and never semantic-clean', () => {
        const receipts = [
            degradedLspReceipt('Simple LSP WASM artifact is unavailable', 'fixture'),
            degradedLspReceipt('Native LSP mode is not supported in browser hosts'),
        ];
        for (const receipt of receipts) {
            assert.strictEqual(receipt.authority, 'degraded');
            assert.strictEqual(receipt.coverage, 'syntax-only');
            assert.strictEqual(receipt.fallbackActive, true);
            assert.match(receipt.message, /not a semantic-clean result/);
        }
        assert.strictEqual(authoritativeLspReceipt('wasm').coverage, 'semantic');
        assert.strictEqual(authoritativeLspReceipt('native').coverage, 'semantic');
    });

    test('opens the canonical workspace fixture and produces stable fallback structure', async () => {
        const workspace = vscode.workspace.workspaceFolders?.[0];
        assert.ok(workspace, 'configured VS Code fixture workspace must exist');
        const fixture = vscode.Uri.file(path.join(workspace.uri.fsPath, 'canonical-parity.spl'));
        const document = await vscode.workspace.openTextDocument(fixture);
        const result = analyzeDocument(document);

        assert.deepStrictEqual(result.symbols.map((symbol) => symbol.name), [
            'browser_workspace_symbol',
            'canonical browser workspace fixture',
            'is visible to native and browser fallback analysis',
        ]);
        assert.deepStrictEqual(result.tests.map((test) => `${test.kind}:${test.label}`), [
            'describe:canonical browser workspace fixture',
            'it:is visible to native and browser fallback analysis',
        ]);
        assert.ok(result.folds.length >= 2);
    });
});
