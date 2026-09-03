"use strict";
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
const path = __importStar(require("path"));
const vscode = __importStar(require("vscode"));
const simpleAnalysisIndex_1 = require("../../analysis/simpleAnalysisIndex");
const simpleLspCapabilityReceipt_1 = require("../../lsp/simpleLspCapabilityReceipt");
const simpleLspServerResolver_1 = require("../../services/simpleLspServerResolver");
suite('browser and WASM canonical parity', () => {
    test('uses one selector for file, untitled, and virtual workspaces', () => {
        assert.deepStrictEqual((0, simpleLspServerResolver_1.createSimpleLspDocumentSelector)(), [
            { scheme: 'file', language: 'simple' },
            { scheme: 'untitled', language: 'simple' },
            { scheme: 'vscode-vfs', language: 'simple' },
        ]);
    });
    test('labels fallback output as syntax-only and never semantic-clean', () => {
        const receipts = [
            (0, simpleLspCapabilityReceipt_1.degradedLspReceipt)('Simple LSP WASM artifact is unavailable', 'fixture'),
            (0, simpleLspCapabilityReceipt_1.degradedLspReceipt)('Native LSP mode is not supported in browser hosts'),
        ];
        for (const receipt of receipts) {
            assert.strictEqual(receipt.authority, 'degraded');
            assert.strictEqual(receipt.coverage, 'syntax-only');
            assert.strictEqual(receipt.fallbackActive, true);
            assert.match(receipt.message, /not a semantic-clean result/);
        }
        assert.strictEqual((0, simpleLspCapabilityReceipt_1.authoritativeLspReceipt)('wasm').coverage, 'semantic');
        assert.strictEqual((0, simpleLspCapabilityReceipt_1.authoritativeLspReceipt)('native').coverage, 'semantic');
    });
    test('opens the canonical workspace fixture and produces stable fallback structure', async () => {
        const workspace = vscode.workspace.workspaceFolders?.[0];
        assert.ok(workspace, 'configured VS Code fixture workspace must exist');
        const fixture = vscode.Uri.file(path.join(workspace.uri.fsPath, 'canonical-parity.spl'));
        const document = await vscode.workspace.openTextDocument(fixture);
        const result = (0, simpleAnalysisIndex_1.analyzeDocument)(document);
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
//# sourceMappingURL=browserWasmParity.test.js.map