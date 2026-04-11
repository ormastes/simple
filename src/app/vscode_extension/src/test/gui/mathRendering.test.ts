import * as fs from 'fs';
import { execFileSync } from 'child_process';
import * as os from 'os';
import * as path from 'path';
import * as assert from 'assert';
import * as vscode from 'vscode';
import { suite, teardown, test } from 'mocha';
import {
    buildMathCustomEditorHtml,
    buildMathCustomEditorState,
    detectMathBlocksInSource,
    findMathBlockAtOffset,
} from '../../math/mathCustomEditor';
import { MathDecorationProvider, buildSvgDecorationLayout, formatSvgDecorationLayoutLog } from '../../math/mathDecorationProvider';
import { MathCoreWasmBridge } from '../../math/mathCoreWasm';
import { MathHoverProvider } from '../../math/mathHoverProvider';
import { buildMathPreviewHtml } from '../../math/mathPreviewPanel';
import { renderToSvgFile } from '../../math/mathSvgRenderer';
import { buildMathSyncPanelHtml, findMathBlockAtPosition, MathSyncPanel } from '../../math/mathSyncPanel';
import { TestUtils } from '../helpers/testUtils';

/** Shared fake decoration provider for hover tests */
function makeFakeDecorationProvider() {
    return {
        detectMathBlocks: () => [
            {
                content: 'frac(1, 2) + x',
                fullRange: new vscode.Range(1, 12, 1, 30),
            },
        ],
    } as any;
}

function getExtensionRoot(): string {
    return path.resolve(__dirname, '../../..');
}

function ensureMathCoreWasmArtifact(extensionRoot: string): boolean {
    const artifactPath = path.join(extensionRoot, 'wasm', 'math-core.wasm');
    if (fs.existsSync(artifactPath)) {
        return true;
    }

    try {
        execFileSync('npm', ['run', 'build:math-core-wasm'], {
            cwd: extensionRoot,
            stdio: 'pipe',
        });
    } catch {
        return false;
    }

    return fs.existsSync(artifactPath);
}

suite('GUI - Math Rendering', function() {
    this.timeout(30000);

    teardown(async () => {
        await TestUtils.closeAllEditors();
        TestUtils.deleteTestFile('test-math-rendering.spl');
        TestUtils.deleteTestFile('test-math-custom-editor.spl');
        TestUtils.deleteTestFile('test-math-sync-panel.spl');
        TestUtils.deleteTestFile('test-math-sync-panel-auto-open.spl');
    });

    test('Decoration provider detects math-mode blocks', async () => {
        const document = await TestUtils.createTestFile(
            'test-math-rendering.spl',
            'let a = m{ alpha + beta }\nlet b = loss{ sqrt(x) }\nlet c = nograd{ sin(theta) }'
        );

        const provider = new MathDecorationProvider();
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

    test('Fallback hover renders math blocks when LSP mode is disabled', async () => {
        const document = await TestUtils.createTestFile(
            'test-math-rendering.spl',
            'fn main():\n    val y = m{ frac(1, 2) + x }\n'
        );

        const provider = new MathHoverProvider(makeFakeDecorationProvider(), new MathCoreWasmBridge());
        provider.setLspRunning(false);

        const hover = await provider.provideHover(
            document,
            new vscode.Position(1, 18),
            {} as vscode.CancellationToken
        ) as vscode.Hover;

        assert.ok(hover, 'expected hover for math block');
        const markdown = hover.contents[0] as vscode.MarkdownString;
        assert.ok(markdown.value.includes('Math Block'));
        assert.ok(markdown.value.includes('frac(1, 2) + x'));
        assert.ok(markdown.value.includes('Pretty:'));
    });

    test('Fallback hover defers when LSP mode is enabled', async () => {
        const document = await TestUtils.createTestFile(
            'test-math-rendering.spl',
            'fn main():\n    val y = m{ frac(1, 2) + x }\n'
        );

        const provider = new MathHoverProvider(makeFakeDecorationProvider(), new MathCoreWasmBridge());
        provider.setLspRunning(true);

        const hover = provider.provideHover(
            document,
            new vscode.Position(1, 18),
            {} as vscode.CancellationToken
        );

        assert.strictEqual(hover, null);
    });

    test('Pure-Simple math-core wasm bridge renders structured JSON when staged artifact is available', async function() {
        const extensionRoot = getExtensionRoot();
        if (!ensureMathCoreWasmArtifact(extensionRoot)) {
            this.skip();
            return;
        }

        const bridge = new MathCoreWasmBridge();
        await bridge.initialize(vscode.Uri.file(extensionRoot));

        assert.strictEqual(
            bridge.isReady(),
            true,
            bridge.getUnavailableReason() ?? 'expected pure-Simple math-core wasm bridge to be ready'
        );

        const result = await bridge.render('frac(1, 2) + alpha^2');

        assert.ok(result, 'expected structured JSON result from wasm bridge');
        assert.strictEqual(result!.latex, '\\frac{1}{2} + \\alpha^2');
        assert.strictEqual(result!.text, '1 / 2 + alpha^2');
        assert.strictEqual(result!.pretty, '(1)/(2) + α²');
        assert.ok(result!.debug?.includes('Add(Frac('), 'expected debug tree to be present');
    });

    test('Preview panel HTML stays offline-safe and contains rendered content', () => {
        const html = buildMathPreviewHtml('x^{2} + 1', 'm{ x^2 + 1 }');

        assert.ok(html.includes('Math Preview'));
        // KaTeX renders to HTML spans — check for katex class or the source in source-block
        assert.ok(
            html.includes('katex') || html.includes('x^{2} + 1'),
            'Should contain KaTeX-rendered output or raw LaTeX'
        );
        assert.ok(html.includes('m{ x^2 + 1 }'), 'Should contain source block');
        assert.ok(html.includes('Rendered'));
        assert.ok(html.includes('Source'));
        assert.ok(!html.includes('cdn.jsdelivr.net'));
        assert.ok(!html.includes('<script src='));
    });

    test('Preview panel HTML uses webview CSP source for KaTeX assets', () => {
        const cssUri = 'vscode-webview-resource://test/katex.min.css';
        const cspSource = 'vscode-webview://test-source';
        const html = buildMathPreviewHtml('x^{2} + 1', 'm{ x^2 + 1 }', cssUri, cspSource);

        assert.ok(html.includes(`<link rel="stylesheet" href="${cssUri}">`));
        assert.ok(html.includes(`style-src ${cspSource} 'unsafe-inline'`));
        assert.ok(html.includes(`font-src ${cspSource}`));
        assert.ok(!html.includes(`style-src ${cssUri}`), 'CSP should use webview.cspSource, not a concrete CSS URI');
    });

    test('Custom editor HTML uses webview CSP source and contains the source shell', () => {
        const cssUri = 'vscode-webview-resource://test/katex.min.css';
        const webviewJsUri = 'vscode-webview-resource://test/mathEditor.js';
        const cspSource = 'vscode-webview://test-source';
        const nonce = 'dGVzdG5vbmNl';
        const html = buildMathCustomEditorHtml(cssUri, webviewJsUri, cspSource, nonce);

        assert.ok(html.includes('Simple Math Source Editor'));
        assert.ok(html.includes('editor-container'));
        assert.ok(html.includes('Math Preview'));
        assert.ok(html.includes('Status'));
        assert.ok(html.includes(`<link rel="stylesheet" href="${cssUri}">`));
        assert.ok(html.includes(`src="${webviewJsUri}"`));
        assert.ok(html.includes(`style-src ${cspSource} 'unsafe-inline'`));
        assert.ok(html.includes(`font-src ${cspSource}`));
        assert.ok(!html.includes(`style-src ${cssUri}`));
        assert.ok(html.includes(`script-src ${cspSource}`), 'CSP script-src must include cspSource for external webview JS');
        assert.ok(html.includes('MathEditorWebview.boot()'));
    });

    test('Custom editor state reports info status when no math block is active', () => {
        const state = buildMathCustomEditorState(
            'file:///tmp/demo.spl',
            'fn main():\n    val y = 42\n',
            0,
            0,
        );

        assert.strictEqual(state.hasActiveBlock, false);
        assert.strictEqual(state.activeBlockStatusKind, 'info');
        assert.ok(state.activeBlockStatusMessage.includes('Move the caret into a math block'));
    });

    test('Custom editor state reports success for renderable math', () => {
        const source = 'fn main():\n    val y = m{ frac(1, 2) + sqrt(x) }\n';
        const state = buildMathCustomEditorState(
            'file:///tmp/demo.spl',
            source,
            source.indexOf('frac'),
            source.indexOf('frac'),
        );

        assert.strictEqual(state.hasActiveBlock, true);
        assert.strictEqual(state.activeBlockStatusKind, 'ok');
        assert.strictEqual(state.activeBlockStatusMessage, 'Rendered active math block.');
        assert.ok(state.activeBlockRenderedHtml.includes('katex'));
    });

    test('Custom editor state reports an error fallback for malformed math', () => {
        const source = 'fn main():\n    val y = m{ alpha ^ }\n';
        const state = buildMathCustomEditorState(
            'file:///tmp/demo.spl',
            source,
            source.indexOf('alpha'),
            source.indexOf('alpha'),
        );

        assert.strictEqual(state.hasActiveBlock, true);
        assert.strictEqual(state.activeBlockStatusKind, 'error');
        assert.ok(state.activeBlockStatusMessage.includes('KaTeX parse error'));
        assert.ok(state.activeBlockRenderedHtml.includes('Could not render the active math block.'));
        assert.ok(state.activeBlockRenderedHtml.includes('\\alpha ^'));
    });

    test('Custom editor math scanner resolves the block under the caret offset', () => {
        const source = 'let a = m{ alpha + beta }\\nlet b = loss{ sqrt(x) }';
        const blocks = detectMathBlocksInSource(source);

        assert.strictEqual(blocks.length, 2);
        assert.strictEqual(blocks[0].blockType, 'math');
        assert.strictEqual(blocks[1].blockType, 'loss');

        const active = findMathBlockAtOffset(source, source.indexOf('sqrt'));
        assert.ok(active, 'expected active math block');
        assert.strictEqual(active?.blockType, 'loss');
        assert.strictEqual(active?.content, 'sqrt(x)');
    });

    test('Complex math blocks render tall KaTeX structures (fractions, roots, multi-row)', () => {
        const source = [
            'let a = m{frac(frac(1, 2) + frac(3, 4), frac(5, 6) * frac(7, 8))}',
            'let b = m{sqrt(frac(x^2 + 1, x^2 - 1))}',
            'let c = m{cases(x, x geq 0; 0, otherwise)}',
            'let d = m{sum(frac(1, k^2), k=1..n)}',
            'let e = m{pi * r^2}',
        ].join('\n');

        const blocks = detectMathBlocksInSource(source);
        assert.strictEqual(blocks.length, 5, 'expected five math blocks');

        // All blocks must produce non-empty renderedHtml with katex class
        for (const block of blocks) {
            assert.ok(block.renderedHtml.length > 0, `block "${block.content}" should have renderedHtml`);
            assert.ok(block.renderedHtml.includes('katex'), `block "${block.content}" should contain katex class`);
        }

        // Nested fraction — must contain frac-line elements (vertical stacking = tall)
        const nestedFrac = blocks[0];
        assert.strictEqual(nestedFrac.content, 'frac(frac(1, 2) + frac(3, 4), frac(5, 6) * frac(7, 8))');
        assert.ok(nestedFrac.renderedHtml.includes('frac-line'), 'nested fraction should render frac-line elements');

        // Square root of fraction — must have both sqrt and frac structures
        const sqrtFrac = blocks[1];
        assert.strictEqual(sqrtFrac.content, 'sqrt(frac(x^2 + 1, x^2 - 1))');
        assert.ok(sqrtFrac.renderedHtml.includes('sqrt'), 'sqrt(frac) should render sqrt element');
        assert.ok(sqrtFrac.renderedHtml.includes('frac-line'), 'sqrt(frac) should render frac-line element');

        // Cases/piecewise — must have multi-row table structure
        const piecewise = blocks[2];
        assert.strictEqual(piecewise.content, 'cases(x, x geq 0; 0, otherwise)');
        assert.ok(
            piecewise.renderedHtml.includes('mtable') || piecewise.renderedHtml.includes('arraycolsep'),
            'piecewise should render multi-row table structure'
        );

        // Summation with fraction body — must have frac-line
        const sumFrac = blocks[3];
        assert.strictEqual(sumFrac.content, 'sum(frac(1, k^2), k=1..n)');
        assert.ok(sumFrac.renderedHtml.includes('frac-line'), 'sum with frac body should render frac-line');

        // Simple inline — must NOT contain tall structures (no frac-line, no sqrt, no mtable)
        const simple = blocks[4];
        assert.strictEqual(simple.content, 'pi * r^2');
        assert.ok(!simple.renderedHtml.includes('frac-line'), 'simple expression should not have frac-line');
        assert.ok(!simple.renderedHtml.includes('mtable'), 'simple expression should not have mtable');
    });

    test('SVG renderer normalizes MathJax dimensions to em units', () => {
        const cacheDir = fs.mkdtempSync(path.join(os.tmpdir(), 'simple-math-svg-'));
        try {
            const result = renderToSvgFile('\\frac{1}{2}', cacheDir, '#cccccc');

            assert.ok(result, 'expected SVG render result');
            assert.ok(result!.heightEm > 0);
            assert.ok(result!.descentEm >= 0);
            assert.ok(result!.widthEm > 0);

            const svgPath = result!.uri.fsPath;
            const svg = fs.readFileSync(svgPath, 'utf8');

            assert.ok(/height="[\d.]+em"/.test(svg), 'expected SVG height to use em units');
            assert.ok(/width="[\d.]+em"/.test(svg), 'expected SVG width to use em units');
            assert.ok(!/height="[\d.]+ex"/.test(svg), 'expected SVG height to avoid ex units');
            assert.ok(!/width="[\d.]+ex"/.test(svg), 'expected SVG width to avoid ex units');
        } finally {
            fs.rmSync(cacheDir, { recursive: true, force: true });
        }
    });

    test('SVG renderer clamps very tall equations', () => {
        const cacheDir = fs.mkdtempSync(path.join(os.tmpdir(), 'simple-math-svg-'));
        try {
            const result = renderToSvgFile(
                '\\frac{\\frac{\\frac{1}{2}}{\\frac{3}{4}}}{\\frac{\\frac{5}{6}}{\\frac{7}{8}}}',
                cacheDir,
                '#cccccc'
            );

            assert.ok(result, 'expected SVG render result');
            assert.ok(result!.heightEm <= 3.01, 'expected clamped height');

            const svgPath = result!.uri.fsPath;
            const svg = fs.readFileSync(svgPath, 'utf8');
            const heightMatch = svg.match(/height="([\d.]+)em"/);
            assert.ok(heightMatch, 'expected serialized SVG height');
            assert.strictEqual(heightMatch![1], result!.heightEm.toFixed(3));
            assert.ok(parseFloat(heightMatch![1]) <= 3.01, 'expected clamped SVG height');
        } finally {
            fs.rmSync(cacheDir, { recursive: true, force: true });
        }
    });

    test('SVG layout scales tall expressions down to fit a single editor line', () => {
        const layout = buildSvgDecorationLayout(
            'frac(1, 2) + sqrt(x)',
            {
                uri: vscode.Uri.file('/tmp/math.svg'),
                heightEm: 2.4,
                descentEm: 0.18,
                widthEm: 3.1,
            },
            'center'
        );

        assert.strictEqual(layout.fitApplied, true);
        assert.ok(layout.height.endsWith('em'));
        assert.ok(layout.width.endsWith('em'));
        assert.ok(Number.parseFloat(layout.height) <= 1.31);
        assert.ok(Number.parseFloat(layout.width) < 3.1);
        const logLine = formatSvgDecorationLayoutLog('frac(1, 2) + sqrt(x)', layout);
        assert.ok(logLine.includes('eq="frac(1, 2) + sqrt(x)"'));
        assert.ok(logLine.includes('height='));
        assert.ok(logLine.includes('fit=yes'));
    });

    test('SVG layout preserves intrinsic size for short expressions', () => {
        const layout = buildSvgDecorationLayout(
            'x + y',
            {
                uri: vscode.Uri.file('/tmp/math.svg'),
                heightEm: 1.0,
                descentEm: 0.12,
                widthEm: 1.5,
            },
            'center'
        );

        assert.strictEqual(layout.fitApplied, false);
        assert.strictEqual(layout.inlineScale, 1.0);
        assert.strictEqual(layout.height, '1.00em');
        assert.strictEqual(layout.width, '1.50em');
        const logLine = formatSvgDecorationLayoutLog('x + y', layout);
        assert.ok(logLine.includes('eq="x + y"'));
        assert.ok(logLine.includes('scale='));
        assert.ok(logLine.includes('fit=no'));
    });

    test('SVG layout keeps bottom alignment tied to scaled descent', () => {
        const layout = buildSvgDecorationLayout(
            'frac(1, 2) + frac(3, 4)',
            {
                uri: vscode.Uri.file('/tmp/math.svg'),
                heightEm: 2.0,
                descentEm: 0.4,
                widthEm: 1.6,
            },
            'bottom'
        );

        assert.strictEqual(layout.fitApplied, true);
        assert.strictEqual(layout.verticalAlign, '-0.26em');
        const logLine = formatSvgDecorationLayoutLog('frac(1, 2) + frac(3, 4)', layout);
        assert.ok(logLine.includes('align=-0.26em'));
    });

    test('SVG layout keeps a readable minimum size for small inputs', () => {
        const layout = buildSvgDecorationLayout(
            'i',
            {
                uri: vscode.Uri.file('/tmp/math.svg'),
                heightEm: 0.4,
                descentEm: 0.05,
                widthEm: 0.2,
            },
            'center'
        );

        assert.strictEqual(layout.fitApplied, false);
        assert.strictEqual(layout.height, '0.92em');
        assert.strictEqual(layout.width, '0.75em');
    });

    test('Math sync panel HTML contains editable source and sync hooks', () => {
        const html = buildMathSyncPanelHtml({
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

    test('Math sync panel HTML uses webview CSP source for KaTeX assets', () => {
        const cssUri = 'vscode-webview-resource://test/katex.min.css';
        const cspSource = 'vscode-webview://test-source';
        const html = buildMathSyncPanelHtml({
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

    test('Math sync panel HTML renders empty state when no block is active', () => {
        const html = buildMathSyncPanelHtml({
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

    test('Math sync panel block lookup finds the active math block', async () => {
        const document = await TestUtils.createTestFile(
            'test-math-sync-panel.spl',
            'fn main():\n    val y = m{ frac(1, 2) + sqrt(x) }\n    val z = 42\n'
        );

        const provider = new MathDecorationProvider();
        const block = findMathBlockAtPosition(provider, document, new vscode.Position(1, 18));

        assert.ok(block, 'expected active math block');
        assert.strictEqual(block!.content, 'frac(1, 2) + sqrt(x)');

        provider.dispose();
    });

    test('Math sync panel auto-opens when the caret enters a math block', async () => {
        await vscode.workspace.getConfiguration('simple').update(
            'math.syncPanel.autoOpen',
            true,
            vscode.ConfigurationTarget.Global
        );

        const document = await TestUtils.createTestFile(
            'test-math-sync-panel-auto-open.spl',
            'fn main():\n    val y = m{ frac(1, 2) + sqrt(x) }\n    val z = 42\n'
        );

        const editor = vscode.window.activeTextEditor;
        assert.ok(editor, 'expected active editor');
        MathSyncPanel.close();
        await TestUtils.setCursorPosition(editor!, 1, 18);

        await TestUtils.waitFor(() => MathSyncPanel.isVisible(), 5000, 50);
        assert.strictEqual(MathSyncPanel.isVisible(), true);

        await vscode.workspace.getConfiguration('simple').update(
            'math.syncPanel.autoOpen',
            false,
            vscode.ConfigurationTarget.Global
        );
        MathSyncPanel.close();
        void document;
    });

    test('Custom editor opens a .spl document with the custom view type', async () => {
        const document = await TestUtils.createTestFile(
            'test-math-custom-editor.spl',
            'fn main():\n    val y = m{ frac(1, 2) + sqrt(x) }\n'
        );

        await vscode.commands.executeCommand('vscode.openWith', document.uri, 'simple.mathSourceEditor');

        await TestUtils.waitFor(() => {
            const tab = vscode.window.tabGroups.activeTabGroup.activeTab;
            const input = tab?.input as { viewType?: string } | undefined;
            return input?.viewType === 'simple.mathSourceEditor';
        }, 5000, 50);

        const tab = vscode.window.tabGroups.activeTabGroup.activeTab;
        const input = tab?.input as { viewType?: string } | undefined;
        assert.strictEqual(input?.viewType, 'simple.mathSourceEditor');
    });
});
