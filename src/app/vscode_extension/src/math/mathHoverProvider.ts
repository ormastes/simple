/**
 * Math Hover Provider (fallback mode)
 *
 * Provides hover information for `m{ }` math blocks in Simple source files.
 * When the user hovers over a math block, shows:
 * - The math expression formatted nicely
 * - A link to open the preview panel
 *
 * IMPORTANT: The LSP server (src/app/lsp/handlers/hover.spl) already provides
 * full math hover with render_latex_raw() and to_pretty() from the Simple runtime.
 * This provider acts as a FALLBACK when the LSP is not connected. When the LSP
 * is running, it handles math hover natively and this provider defers to it.
 */

import * as vscode from 'vscode';
import { MathDecorationProvider } from './mathDecorationProvider';
import { simpleToLatex, simpleToUnicode } from './mathConverter';

export class MathHoverProvider implements vscode.HoverProvider {
    private lspRunning: boolean = false;

    constructor(private decorationProvider: MathDecorationProvider) {}

    /**
     * Set whether the LSP client is currently running.
     * When the LSP is running, its hover handler (src/app/lsp/handlers/hover.spl)
     * provides math block rendering, so this provider defers to it.
     */
    public setLspRunning(running: boolean): void {
        this.lspRunning = running;
    }

    /**
     * Provide hover information for math blocks.
     *
     * When the LSP is running, returns null to let the LSP hover handler
     * (src/app/lsp/handlers/hover.spl) provide the response instead.
     * Acts as fallback when LSP is not connected.
     */
    public provideHover(
        document: vscode.TextDocument,
        position: vscode.Position,
        _token: vscode.CancellationToken
    ): vscode.ProviderResult<vscode.Hover> {
        // When LSP is running, defer to its hover handler which provides
        // full rendering via render_latex_raw() and to_pretty() from
        // src/app/lsp/handlers/hover.spl
        if (this.lspRunning) {
            return null;
        }

        const config = vscode.workspace.getConfiguration('simple');
        if (!config.get<boolean>('math.previewOnHover', true)) {
            return null;
        }

        const mathBlocks = this.decorationProvider.detectMathBlocks(document);

        for (const block of mathBlocks) {
            if (block.fullRange.contains(position)) {
                return this.createHover(block.content, block.fullRange);
            }
        }

        return null;
    }

    /**
     * Create a hover display for a math block (fallback mode).
     *
     * Uses local TypeScript converters from mathConverter.ts which mirror
     * the Simple-side rendering in src/lib/math_repr.spl.
     */
    private createHover(content: string, range: vscode.Range): vscode.Hover {
        const markdown = new vscode.MarkdownString();
        markdown.isTrusted = true;
        markdown.supportHtml = true;

        // Header
        markdown.appendMarkdown('**Math Block** `m{ }`\n\n');
        markdown.appendMarkdown('---\n\n');

        // Display math via VSCode's built-in KaTeX rendering
        const latex = simpleToLatex(content);
        markdown.appendMarkdown(`$$${latex}$$\n\n`);

        // Separator
        markdown.appendMarkdown('---\n\n');

        // Unicode pretty text (mirrors to_pretty() from src/lib/math_repr.spl)
        const pretty = simpleToUnicode(content);
        markdown.appendMarkdown(`**Pretty:** ${pretty}\n\n`);

        // Source
        markdown.appendMarkdown(`**Source:** \`${content}\`\n\n`);

        // Action link to open preview panel
        const openPreviewCommand = vscode.Uri.parse(
            `command:simple.math.togglePreview`
        );
        markdown.appendMarkdown(
            `[Open Math Preview Panel](${openPreviewCommand})`
        );

        return new vscode.Hover(markdown, range);
    }
}
