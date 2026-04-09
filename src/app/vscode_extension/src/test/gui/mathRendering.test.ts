import * as assert from 'assert';
import * as vscode from 'vscode';
import { suite, teardown, test } from 'mocha';
import { MathDecorationProvider } from '../../math/mathDecorationProvider';
import { MathHoverProvider } from '../../math/mathHoverProvider';
import { buildMathPreviewHtml } from '../../math/mathPreviewPanel';
import { TestUtils } from '../helpers/testUtils';

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

        const fakeDecorationProvider = {
            detectMathBlocks: () => [
                {
                    content: 'frac(1, 2) + x',
                    fullRange: new vscode.Range(1, 12, 1, 30),
                },
            ],
        } as any;

        const provider = new MathHoverProvider(fakeDecorationProvider);
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

        const fakeDecorationProvider = {
            detectMathBlocks: () => [
                {
                    content: 'frac(1, 2) + x',
                    fullRange: new vscode.Range(1, 12, 1, 30),
                },
            ],
        } as any;

        const provider = new MathHoverProvider(fakeDecorationProvider);
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
});
