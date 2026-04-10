import * as fs from 'fs';
import { execFileSync } from 'child_process';
import * as os from 'os';
import * as path from 'path';
import * as assert from 'assert';
import * as vscode from 'vscode';
import { suite, teardown, test } from 'mocha';
import { MathDecorationProvider, buildSvgDecorationLayout, formatSvgDecorationLayoutLog } from '../../math/mathDecorationProvider';
import { MathCoreWasmBridge } from '../../math/mathCoreWasm';
import { MathHoverProvider } from '../../math/mathHoverProvider';
import { buildMathPreviewHtml } from '../../math/mathPreviewPanel';
import { renderSpacerSvgFile, renderToSvgFile } from '../../math/mathSvgRenderer';
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

    test('SVG layout boosts fractions and roots for visibility', () => {
        const layout = buildSvgDecorationLayout(
            'frac(1, 2) + sqrt(x)',
            {
                uri: vscode.Uri.file('/tmp/math.svg'),
                heightEm: 1.25,
                descentEm: 0.18,
                widthEm: 2.0,
            },
            'center'
        );

        assert.strictEqual(layout.boostApplied, true);
        assert.ok(layout.height.endsWith('em'));
        assert.ok(layout.width.endsWith('em'));
        assert.ok(layout.spacerHeight.endsWith('em'));
        assert.ok(Number.parseFloat(layout.height) > 1.25);
        assert.ok(Number.parseFloat(layout.spacerHeight) > Number.parseFloat(layout.height));
        const logLine = formatSvgDecorationLayoutLog('frac(1, 2) + sqrt(x)', layout);
        assert.ok(logLine.includes('eq="frac(1, 2) + sqrt(x)"'));
        assert.ok(logLine.includes('height='));
        assert.ok(logLine.includes('spacer='));
        assert.ok(logLine.includes('boost=yes'));
    });

    test('SVG layout boosts nested fractions more aggressively', () => {
        const layout = buildSvgDecorationLayout(
            'frac(1, 2) + frac(3, 4) + sqrt(x)',
            {
                uri: vscode.Uri.file('/tmp/math.svg'),
                heightEm: 1.0,
                descentEm: 0.18,
                widthEm: 1.5,
            },
            'bottom'
        );

        assert.strictEqual(layout.boostApplied, true);
        assert.ok(layout.layoutScale > 1.0);
        assert.ok(layout.layoutScale >= 1.2);
        assert.ok(Number.parseFloat(layout.spacerHeight) > Number.parseFloat(layout.height));
        const logLine = formatSvgDecorationLayoutLog('frac(1, 2) + frac(3, 4) + sqrt(x)', layout);
        assert.ok(logLine.includes('eq="frac(1, 2) + frac(3, 4) + sqrt(x)"'));
        assert.ok(logLine.includes('scale='));
        assert.ok(logLine.includes('align=-0.18em'));
    });

    test('SVG layout does not boost plain division arithmetic', () => {
        const layout = buildSvgDecorationLayout(
            'a / b + c / d',
            {
                uri: vscode.Uri.file('/tmp/math.svg'),
                heightEm: 1.0,
                descentEm: 0.12,
                widthEm: 1.6,
            },
            'center'
        );

        assert.strictEqual(layout.boostApplied, false);
        assert.strictEqual(layout.layoutScale, 1.0);
        assert.strictEqual(layout.spacerHeight, layout.height);
        const logLine = formatSvgDecorationLayoutLog('a / b + c / d', layout);
        assert.ok(logLine.includes('eq="a / b + c / d"'));
        assert.ok(logLine.includes('boost=no'));
    });

    test('SVG layout height is larger for roots and fractions than plain division', () => {
        const plain = buildSvgDecorationLayout(
            'a / b',
            {
                uri: vscode.Uri.file('/tmp/math.svg'),
                heightEm: 1.0,
                descentEm: 0.12,
                widthEm: 1.4,
            },
            'center'
        );
        const boosted = buildSvgDecorationLayout(
            'frac(1, 2) + sqrt(x)',
            {
                uri: vscode.Uri.file('/tmp/math.svg'),
                heightEm: 1.0,
                descentEm: 0.12,
                widthEm: 1.4,
            },
            'center'
        );

        assert.strictEqual(plain.layoutScale, 1.0);
        assert.ok(Number.parseFloat(plain.height) <= 1.01);
        assert.ok(boosted.layoutScale > plain.layoutScale);
        assert.ok(Number.parseFloat(boosted.height) > Number.parseFloat(plain.height));
        assert.ok(formatSvgDecorationLayoutLog('a / b', plain).includes('height='));
        assert.ok(formatSvgDecorationLayoutLog('frac(1, 2) + sqrt(x)', boosted).includes('boost=yes'));
    });

    test('SVG spacer renderer creates a transparent em-sized box', () => {
        const cacheDir = fs.mkdtempSync(path.join(os.tmpdir(), 'simple-math-svg-'));
        try {
            const result = renderSpacerSvgFile(cacheDir, 1.5, 0.01);

            assert.ok(result, 'expected spacer render result');
            assert.ok(result!.heightEm >= 1.5);
            assert.ok(result!.widthEm >= 0.01);

            const svgPath = result!.uri.fsPath;
            const svg = fs.readFileSync(svgPath, 'utf8');

            assert.ok(svg.includes('fill="transparent"'));
            assert.ok(/height="[\d.]+em"/.test(svg), 'expected spacer SVG height to use em units');
            assert.ok(/width="[\d.]+em"/.test(svg), 'expected spacer SVG width to use em units');
        } finally {
            fs.rmSync(cacheDir, { recursive: true, force: true });
        }
    });

    test('SVG layout gives roots a larger spacer than simple fractions', () => {
        const fracOnly = buildSvgDecorationLayout(
            'frac(1, 2)',
            {
                uri: vscode.Uri.file('/tmp/math.svg'),
                heightEm: 1.0,
                descentEm: 0.12,
                widthEm: 1.2,
            },
            'center'
        );
        const sqrtOnly = buildSvgDecorationLayout(
            'sqrt(x)',
            {
                uri: vscode.Uri.file('/tmp/math.svg'),
                heightEm: 1.0,
                descentEm: 0.12,
                widthEm: 1.2,
            },
            'center'
        );

        assert.ok(Number.parseFloat(sqrtOnly.spacerHeight) > Number.parseFloat(fracOnly.spacerHeight));
        assert.ok(Number.parseFloat(sqrtOnly.height) > Number.parseFloat(fracOnly.height));
        assert.ok(Number.parseFloat(fracOnly.spacerHeight) >= 1.28);
        assert.ok(Number.parseFloat(sqrtOnly.spacerHeight) >= 1.28);
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
});
