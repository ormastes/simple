import * as assert from 'assert';
import * as path from 'path';
import * as vscode from 'vscode';
import { analyzeDocument } from '../../analysis/simpleAnalysisIndex';
import { authoritativeLspReceipt, degradedLspReceipt } from '../../lsp/simpleLspCapabilityReceipt';
import { createSimpleLspDocumentSelector } from '../../services/simpleLspServerResolver';
import { KpfToolingSession } from '../../kpf';
import { loadCanonicalToolingConformanceV1 } from '../support/canonicalToolingConformance';

suite('browser and WASM canonical parity', () => {
    test('browser/WASM adapter consumes the canonical receipt and snapshot corpus', async () => {
        const corpus = await loadCanonicalToolingConformanceV1();
        const receipt = authoritativeLspReceipt(corpus.browser_source);
        const accepted: string[] = [];
        const session = new KpfToolingSession((batch) => accepted.push(batch.canonicalResultId));
        session.admit({
            providerId: 'simple.language',
            generation: 'generation-7',
            placement: 'wasm',
            capabilities: [{ id: 'ide.language-session', major: 1 }],
            schemaDigest: 'sha256:language-v1',
            admitted: true,
        });
        session.openSnapshot({ uri: corpus.uri, version: corpus.revision, digest: corpus.content_digest });

        assert.strictEqual(receipt.authority, corpus.authority);
        assert.strictEqual(receipt.coverage, corpus.coverage);
        assert.strictEqual(session.acceptDiagnostics({
            snapshot: { uri: corpus.uri, version: corpus.revision, digest: corpus.content_digest },
            canonicalResultId: corpus.canonical_result_id,
            diagnostics: [{ message: 'broken' }],
            semanticCoverageComplete: corpus.semantic_coverage_complete,
        }), true);
        assert.deepStrictEqual(accepted, [corpus.canonical_result_id]);
    });

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
