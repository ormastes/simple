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
const fs = __importStar(require("fs"));
const os = __importStar(require("os"));
const path = __importStar(require("path"));
const assert = __importStar(require("assert"));
const vscode = __importStar(require("vscode"));
const mocha_1 = require("mocha");
const mathDecorationProvider_1 = require("../../math/mathDecorationProvider");
const mathHoverProvider_1 = require("../../math/mathHoverProvider");
const mathPreviewPanel_1 = require("../../math/mathPreviewPanel");
const mathSvgRenderer_1 = require("../../math/mathSvgRenderer");
const testUtils_1 = require("../helpers/testUtils");
/** Shared fake decoration provider for hover tests */
function makeFakeDecorationProvider() {
    return {
        detectMathBlocks: () => [
            {
                content: 'frac(1, 2) + x',
                fullRange: new vscode.Range(1, 12, 1, 30),
            },
        ],
    };
}
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
        const provider = new mathHoverProvider_1.MathHoverProvider(makeFakeDecorationProvider());
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
        const provider = new mathHoverProvider_1.MathHoverProvider(makeFakeDecorationProvider());
        provider.setLspRunning(true);
        const hover = provider.provideHover(document, new vscode.Position(1, 18), {});
        assert.strictEqual(hover, null);
    });
    (0, mocha_1.test)('Preview panel HTML stays offline-safe and contains rendered content', () => {
        const html = (0, mathPreviewPanel_1.buildMathPreviewHtml)('x^{2} + 1', 'm{ x^2 + 1 }');
        assert.ok(html.includes('Math Preview'));
        // KaTeX renders to HTML spans — check for katex class or the source in source-block
        assert.ok(html.includes('katex') || html.includes('x^{2} + 1'), 'Should contain KaTeX-rendered output or raw LaTeX');
        assert.ok(html.includes('m{ x^2 + 1 }'), 'Should contain source block');
        assert.ok(html.includes('Rendered'));
        assert.ok(html.includes('Source'));
        assert.ok(!html.includes('cdn.jsdelivr.net'));
        assert.ok(!html.includes('<script src='));
    });
    (0, mocha_1.test)('SVG renderer normalizes MathJax dimensions to em units', () => {
        const cacheDir = fs.mkdtempSync(path.join(os.tmpdir(), 'simple-math-svg-'));
        try {
            const result = (0, mathSvgRenderer_1.renderToSvgFile)('\\frac{1}{2}', cacheDir, '#cccccc');
            assert.ok(result, 'expected SVG render result');
            assert.ok(result.heightEm > 0);
            assert.ok(result.descentEm >= 0);
            assert.ok(result.widthEm > 0);
            const svgPath = result.uri.fsPath;
            const svg = fs.readFileSync(svgPath, 'utf8');
            assert.ok(/height="[\d.]+em"/.test(svg), 'expected SVG height to use em units');
            assert.ok(/width="[\d.]+em"/.test(svg), 'expected SVG width to use em units');
            assert.ok(!/height="[\d.]+ex"/.test(svg), 'expected SVG height to avoid ex units');
            assert.ok(!/width="[\d.]+ex"/.test(svg), 'expected SVG width to avoid ex units');
        }
        finally {
            fs.rmSync(cacheDir, { recursive: true, force: true });
        }
    });
    (0, mocha_1.test)('SVG renderer clamps very tall equations', () => {
        const cacheDir = fs.mkdtempSync(path.join(os.tmpdir(), 'simple-math-svg-'));
        try {
            const result = (0, mathSvgRenderer_1.renderToSvgFile)('\\frac{\\frac{\\frac{1}{2}}{\\frac{3}{4}}}{\\frac{\\frac{5}{6}}{\\frac{7}{8}}}', cacheDir, '#cccccc');
            assert.ok(result, 'expected SVG render result');
            assert.ok(result.heightEm <= 3.01, 'expected clamped height');
            const svgPath = result.uri.fsPath;
            const svg = fs.readFileSync(svgPath, 'utf8');
            const heightMatch = svg.match(/height="([\d.]+)em"/);
            assert.ok(heightMatch, 'expected serialized SVG height');
            assert.strictEqual(heightMatch[1], result.heightEm.toFixed(3));
            assert.ok(parseFloat(heightMatch[1]) <= 3.01, 'expected clamped SVG height');
        }
        finally {
            fs.rmSync(cacheDir, { recursive: true, force: true });
        }
    });
});
//# sourceMappingURL=mathRendering.test.js.map