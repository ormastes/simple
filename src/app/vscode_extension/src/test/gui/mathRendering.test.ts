import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import * as assert from 'assert';
import * as vscode from 'vscode';
import { suite, teardown, test } from 'mocha';
import { MathDecorationProvider } from '../../math/mathDecorationProvider';
import { MathHoverProvider } from '../../math/mathHoverProvider';
import { buildMathPreviewHtml } from '../../math/mathPreviewPanel';
import { renderToSvgFile } from '../../math/mathSvgRenderer';
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

suite('GUI - Math Rendering', function() {
    this.timeout(30000);

    teardown(async () => {
        await TestUtils.closeAllEditors();
        TestUtils.deleteTestFile('test-math-rendering.spl');
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

        const provider = new MathHoverProvider(makeFakeDecorationProvider());
        provider.setLspRunning(false);

        const hover = provider.provideHover(
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

        const provider = new MathHoverProvider(makeFakeDecorationProvider());
        provider.setLspRunning(true);

        const hover = provider.provideHover(
            document,
            new vscode.Position(1, 18),
            {} as vscode.CancellationToken
        );

        assert.strictEqual(hover, null);
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
});
