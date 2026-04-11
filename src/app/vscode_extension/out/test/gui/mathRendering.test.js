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
const child_process_1 = require("child_process");
const os = __importStar(require("os"));
const path = __importStar(require("path"));
const assert = __importStar(require("assert"));
const vscode = __importStar(require("vscode"));
const mocha_1 = require("mocha");
const mathDecorationProvider_1 = require("../../math/mathDecorationProvider");
const mathCoreWasm_1 = require("../../math/mathCoreWasm");
const mathHoverProvider_1 = require("../../math/mathHoverProvider");
const mathPreviewPanel_1 = require("../../math/mathPreviewPanel");
const mathSvgRenderer_1 = require("../../math/mathSvgRenderer");
const mathSyncPanel_1 = require("../../math/mathSyncPanel");
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
function getExtensionRoot() {
    return path.resolve(__dirname, '../../..');
}
function ensureMathCoreWasmArtifact(extensionRoot) {
    const artifactPath = path.join(extensionRoot, 'wasm', 'math-core.wasm');
    if (fs.existsSync(artifactPath)) {
        return true;
    }
    try {
        (0, child_process_1.execFileSync)('npm', ['run', 'build:math-core-wasm'], {
            cwd: extensionRoot,
            stdio: 'pipe',
        });
    }
    catch {
        return false;
    }
    return fs.existsSync(artifactPath);
}
(0, mocha_1.suite)('GUI - Math Rendering', function () {
    this.timeout(30000);
    (0, mocha_1.teardown)(async () => {
        await testUtils_1.TestUtils.closeAllEditors();
        testUtils_1.TestUtils.deleteTestFile('test-math-rendering.spl');
        testUtils_1.TestUtils.deleteTestFile('test-math-sync-panel.spl');
        testUtils_1.TestUtils.deleteTestFile('test-math-sync-panel-auto-open.spl');
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
        const provider = new mathHoverProvider_1.MathHoverProvider(makeFakeDecorationProvider(), new mathCoreWasm_1.MathCoreWasmBridge());
        provider.setLspRunning(false);
        const hover = await provider.provideHover(document, new vscode.Position(1, 18), {});
        assert.ok(hover, 'expected hover for math block');
        const markdown = hover.contents[0];
        assert.ok(markdown.value.includes('Math Block'));
        assert.ok(markdown.value.includes('frac(1, 2) + x'));
        assert.ok(markdown.value.includes('Pretty:'));
    });
    (0, mocha_1.test)('Fallback hover defers when LSP mode is enabled', async () => {
        const document = await testUtils_1.TestUtils.createTestFile('test-math-rendering.spl', 'fn main():\n    val y = m{ frac(1, 2) + x }\n');
        const provider = new mathHoverProvider_1.MathHoverProvider(makeFakeDecorationProvider(), new mathCoreWasm_1.MathCoreWasmBridge());
        provider.setLspRunning(true);
        const hover = provider.provideHover(document, new vscode.Position(1, 18), {});
        assert.strictEqual(hover, null);
    });
    (0, mocha_1.test)('Pure-Simple math-core wasm bridge renders structured JSON when staged artifact is available', async function () {
        const extensionRoot = getExtensionRoot();
        if (!ensureMathCoreWasmArtifact(extensionRoot)) {
            this.skip();
            return;
        }
        const bridge = new mathCoreWasm_1.MathCoreWasmBridge();
        await bridge.initialize(vscode.Uri.file(extensionRoot));
        assert.strictEqual(bridge.isReady(), true, bridge.getUnavailableReason() ?? 'expected pure-Simple math-core wasm bridge to be ready');
        const result = await bridge.render('frac(1, 2) + alpha^2');
        assert.ok(result, 'expected structured JSON result from wasm bridge');
        assert.strictEqual(result.latex, '\\frac{1}{2} + \\alpha^2');
        assert.strictEqual(result.text, '1 / 2 + alpha^2');
        assert.strictEqual(result.pretty, '(1)/(2) + α²');
        assert.ok(result.debug?.includes('Add(Frac('), 'expected debug tree to be present');
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
    (0, mocha_1.test)('Preview panel HTML uses webview CSP source for KaTeX assets', () => {
        const cssUri = 'vscode-webview-resource://test/katex.min.css';
        const cspSource = 'vscode-webview://test-source';
        const html = (0, mathPreviewPanel_1.buildMathPreviewHtml)('x^{2} + 1', 'm{ x^2 + 1 }', cssUri, cspSource);
        assert.ok(html.includes(`<link rel="stylesheet" href="${cssUri}">`));
        assert.ok(html.includes(`style-src ${cspSource} 'unsafe-inline'`));
        assert.ok(html.includes(`font-src ${cspSource}`));
        assert.ok(!html.includes(`style-src ${cssUri}`), 'CSP should use webview.cspSource, not a concrete CSS URI');
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
    (0, mocha_1.test)('SVG layout scales tall expressions down to fit a single editor line', () => {
        const layout = (0, mathDecorationProvider_1.buildSvgDecorationLayout)('frac(1, 2) + sqrt(x)', {
            uri: vscode.Uri.file('/tmp/math.svg'),
            heightEm: 2.4,
            descentEm: 0.18,
            widthEm: 3.1,
        }, 'center');
        assert.strictEqual(layout.fitApplied, true);
        assert.ok(layout.height.endsWith('em'));
        assert.ok(layout.width.endsWith('em'));
        assert.ok(Number.parseFloat(layout.height) <= 1.31);
        assert.ok(Number.parseFloat(layout.width) < 3.1);
        const logLine = (0, mathDecorationProvider_1.formatSvgDecorationLayoutLog)('frac(1, 2) + sqrt(x)', layout);
        assert.ok(logLine.includes('eq="frac(1, 2) + sqrt(x)"'));
        assert.ok(logLine.includes('height='));
        assert.ok(logLine.includes('fit=yes'));
    });
    (0, mocha_1.test)('SVG layout preserves intrinsic size for short expressions', () => {
        const layout = (0, mathDecorationProvider_1.buildSvgDecorationLayout)('x + y', {
            uri: vscode.Uri.file('/tmp/math.svg'),
            heightEm: 1.0,
            descentEm: 0.12,
            widthEm: 1.5,
        }, 'center');
        assert.strictEqual(layout.fitApplied, false);
        assert.strictEqual(layout.inlineScale, 1.0);
        assert.strictEqual(layout.height, '1.00em');
        assert.strictEqual(layout.width, '1.50em');
        const logLine = (0, mathDecorationProvider_1.formatSvgDecorationLayoutLog)('x + y', layout);
        assert.ok(logLine.includes('eq="x + y"'));
        assert.ok(logLine.includes('scale='));
        assert.ok(logLine.includes('fit=no'));
    });
    (0, mocha_1.test)('SVG layout keeps bottom alignment tied to scaled descent', () => {
        const layout = (0, mathDecorationProvider_1.buildSvgDecorationLayout)('frac(1, 2) + frac(3, 4)', {
            uri: vscode.Uri.file('/tmp/math.svg'),
            heightEm: 2.0,
            descentEm: 0.4,
            widthEm: 1.6,
        }, 'bottom');
        assert.strictEqual(layout.fitApplied, true);
        assert.strictEqual(layout.verticalAlign, '-0.26em');
        const logLine = (0, mathDecorationProvider_1.formatSvgDecorationLayoutLog)('frac(1, 2) + frac(3, 4)', layout);
        assert.ok(logLine.includes('align=-0.26em'));
    });
    (0, mocha_1.test)('SVG layout keeps a readable minimum size for small inputs', () => {
        const layout = (0, mathDecorationProvider_1.buildSvgDecorationLayout)('i', {
            uri: vscode.Uri.file('/tmp/math.svg'),
            heightEm: 0.4,
            descentEm: 0.05,
            widthEm: 0.2,
        }, 'center');
        assert.strictEqual(layout.fitApplied, false);
        assert.strictEqual(layout.height, '0.92em');
        assert.strictEqual(layout.width, '0.75em');
    });
    (0, mocha_1.test)('Math sync panel HTML contains editable source and sync hooks', () => {
        const html = (0, mathSyncPanel_1.buildMathSyncPanelHtml)({
            documentUri: 'file:///tmp/demo.spl',
            blockText: 'frac(1, 2) + sqrt(x)',
            latex: '\\frac{1}{2} + \\sqrt{x}',
            pretty: '(1)/(2) + √x',
            renderedHtml: '<span>rendered</span>',
            blockLabel: 'm{}',
            selectionStart: 2,
            selectionEnd: 5,
            hasContent: true,
        }, vscode.Uri.file('/tmp/katex.css').toString());
        assert.ok(html.includes('Math Sync Panel'));
        assert.ok(html.includes('panel-root'));
        assert.ok(html.includes('active-strip'));
        assert.ok(html.includes('sync-pending'));
        assert.ok(html.includes('math-source'));
        assert.ok(html.includes('selection-highlight'));
        assert.ok(html.includes('request-sync'));
        assert.ok(html.includes('type: \'edit\''));
        assert.ok(html.includes('setSelectionRange'));
        assert.ok(html.includes('rendered'));
        assert.ok(html.includes('frac(1, 2) + sqrt(x)'));
    });
    (0, mocha_1.test)('Math sync panel HTML uses webview CSP source for KaTeX assets', () => {
        const cssUri = 'vscode-webview-resource://test/katex.min.css';
        const cspSource = 'vscode-webview://test-source';
        const html = (0, mathSyncPanel_1.buildMathSyncPanelHtml)({
            documentUri: 'file:///tmp/demo.spl',
            blockText: 'frac(1, 2)',
            latex: '\\frac{1}{2}',
            pretty: '(1)/(2)',
            renderedHtml: '<span>rendered</span>',
            blockLabel: 'm{}',
            selectionStart: 0,
            selectionEnd: 4,
            hasContent: true,
        }, cssUri, cspSource);
        assert.ok(html.includes(`<link rel="stylesheet" href="${cssUri}">`));
        assert.ok(html.includes(`style-src ${cspSource} 'unsafe-inline'`));
        assert.ok(html.includes(`font-src ${cspSource}`));
        assert.ok(!html.includes(`style-src ${cssUri}`), 'CSP should use webview.cspSource, not a concrete CSS URI');
    });
    (0, mocha_1.test)('Math sync panel HTML renders empty state when no block is active', () => {
        const html = (0, mathSyncPanel_1.buildMathSyncPanelHtml)({
            documentUri: 'file:///tmp/demo.spl',
            blockText: '',
            latex: '',
            pretty: '',
            renderedHtml: '',
            blockLabel: 'none',
            selectionStart: 0,
            selectionEnd: 0,
            hasContent: false,
        });
        assert.ok(html.includes('Move the cursor onto a math block in the source editor.'));
        assert.ok(html.includes('panel-root'));
        assert.ok(html.includes('math-source'));
    });
    (0, mocha_1.test)('Math sync panel block lookup finds the active math block', async () => {
        const document = await testUtils_1.TestUtils.createTestFile('test-math-sync-panel.spl', 'fn main():\n    val y = m{ frac(1, 2) + sqrt(x) }\n    val z = 42\n');
        const provider = new mathDecorationProvider_1.MathDecorationProvider();
        const block = (0, mathSyncPanel_1.findMathBlockAtPosition)(provider, document, new vscode.Position(1, 18));
        assert.ok(block, 'expected active math block');
        assert.strictEqual(block.content, 'frac(1, 2) + sqrt(x)');
        provider.dispose();
    });
    (0, mocha_1.test)('Math sync panel auto-opens when the caret enters a math block', async () => {
        await vscode.workspace.getConfiguration('simple').update('math.syncPanel.autoOpen', true, vscode.ConfigurationTarget.Global);
        const document = await testUtils_1.TestUtils.createTestFile('test-math-sync-panel-auto-open.spl', 'fn main():\n    val y = m{ frac(1, 2) + sqrt(x) }\n    val z = 42\n');
        const editor = vscode.window.activeTextEditor;
        assert.ok(editor, 'expected active editor');
        mathSyncPanel_1.MathSyncPanel.close();
        await testUtils_1.TestUtils.setCursorPosition(editor, 1, 18);
        await testUtils_1.TestUtils.waitFor(() => mathSyncPanel_1.MathSyncPanel.isVisible(), 5000, 50);
        assert.strictEqual(mathSyncPanel_1.MathSyncPanel.isVisible(), true);
        await vscode.workspace.getConfiguration('simple').update('math.syncPanel.autoOpen', false, vscode.ConfigurationTarget.Global);
        mathSyncPanel_1.MathSyncPanel.close();
        void document;
    });
});
//# sourceMappingURL=mathRendering.test.js.map