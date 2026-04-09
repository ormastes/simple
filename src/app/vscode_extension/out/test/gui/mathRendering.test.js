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
const vscode = __importStar(require("vscode"));
const mocha_1 = require("mocha");
const mathDecorationProvider_1 = require("../../math/mathDecorationProvider");
const mathHoverProvider_1 = require("../../math/mathHoverProvider");
const mathPreviewPanel_1 = require("../../math/mathPreviewPanel");
const testUtils_1 = require("../helpers/testUtils");
(0, mocha_1.suite)('GUI - Math Rendering', function () {
    this.timeout(30000);
    (0, mocha_1.teardown)(async () => {
        await testUtils_1.TestUtils.closeAllEditors();
        testUtils_1.TestUtils.deleteTestFile('test-math-rendering.spl');
    });
    (0, mocha_1.test)('Decoration provider detects math-mode blocks', async () => {
        const document = await testUtils_1.TestUtils.createTestFile('test-math-rendering.spl', 'let a = m{ alpha + beta }\nlet b = loss{ sqrt(x) }\nlet c = nograd{ sin(theta) }');
        const provider = new mathDecorationProvider_1.MathDecorationProvider();
        const blocks = provider.detectMathBlocks(document);
        assert.strictEqual(blocks.length, 3, 'expected three math blocks');
        assert.strictEqual(blocks[0].blockType, 'math');
        assert.strictEqual(blocks[0].content, 'alpha + beta');
        assert.strictEqual(blocks[1].blockType, 'loss');
        assert.strictEqual(blocks[1].content, 'sqrt(x)');
        assert.strictEqual(blocks[2].blockType, 'nograd');
        assert.strictEqual(blocks[2].content, 'sin(theta)');
        provider.dispose();
    });
    (0, mocha_1.test)('Fallback hover renders math blocks when LSP mode is disabled', async () => {
        const document = await testUtils_1.TestUtils.createTestFile('test-math-rendering.spl', 'fn main():\n    val y = m{ frac(1, 2) + x }\n');
        const fakeDecorationProvider = {
            detectMathBlocks: () => [
                {
                    content: 'frac(1, 2) + x',
                    fullRange: new vscode.Range(1, 12, 1, 30),
                },
            ],
        };
        const provider = new mathHoverProvider_1.MathHoverProvider(fakeDecorationProvider);
        provider.setLspRunning(false);
        const hover = provider.provideHover(document, new vscode.Position(1, 18), {});
        assert.ok(hover, 'expected hover for math block');
        const markdown = hover.contents[0];
        assert.ok(markdown.value.includes('Math Block'));
        assert.ok(markdown.value.includes('frac(1, 2) + x'));
        assert.ok(markdown.value.includes('Pretty:'));
    });
    (0, mocha_1.test)('Fallback hover defers when LSP mode is enabled', async () => {
        const document = await testUtils_1.TestUtils.createTestFile('test-math-rendering.spl', 'fn main():\n    val y = m{ frac(1, 2) + x }\n');
        const fakeDecorationProvider = {
            detectMathBlocks: () => [
                {
                    content: 'frac(1, 2) + x',
                    fullRange: new vscode.Range(1, 12, 1, 30),
                },
            ],
        };
        const provider = new mathHoverProvider_1.MathHoverProvider(fakeDecorationProvider);
        provider.setLspRunning(true);
        const hover = provider.provideHover(document, new vscode.Position(1, 18), {});
        assert.strictEqual(hover, null);
    });
    (0, mocha_1.test)('Preview panel HTML stays offline-safe and contains rendered content', () => {
        const html = (0, mathPreviewPanel_1.buildMathPreviewHtml)('x^{2} + 1', 'm{ x^2 + 1 }');
        assert.ok(html.includes('Math Preview'));
        assert.ok(html.includes('x^{2} + 1'));
        assert.ok(html.includes('m{ x^2 + 1 }'));
        assert.ok(html.includes('Rendered'));
        assert.ok(html.includes('Source'));
        assert.ok(!html.includes('cdn.jsdelivr.net'));
        assert.ok(!html.includes('<script src='));
    });
});
//# sourceMappingURL=mathRendering.test.js.map