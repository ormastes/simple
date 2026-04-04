/**
 * Math Preview Panel - Webview panel for LaTeX math preview
 *
 * Shows a side panel that renders LaTeX for the math block under the cursor.
 * Uses an offline-safe HTML preview inside the webview.
 * Updates automatically when the cursor moves to a different math block.
 *
 * LaTeX conversion mirrors src/lib/math_repr.spl render_latex_raw() for local
 * preview. The full Simple rendering pipeline is:
 *   src/lib/math_repr.spl  - Parser + renderers (to_pretty, render_latex_raw, to_md)
 *   src/lib/mathjax.spl    - MathJax SFFI wrapper (SVG/HTML rendering via Node.js)
 *   src/app/cli/query_visibility.spl - query/LSP hover uses both for server-side rendering
 */

import * as vscode from 'vscode';
import { MathDecorationProvider } from './mathDecorationProvider';
import { simpleToLatex, simpleToUnicode } from './mathConverter';

/**
 * Escape a string for safe embedding in HTML.
 */
function escapeForHtml(text: string): string {
    return text
        .replace(/&/g, '&amp;')
        .replace(/</g, '&lt;')
        .replace(/>/g, '&gt;')
        .replace(/"/g, '&quot;')
        .replace(/'/g, '&#039;');
}

/**
 * Generate offline-safe HTML content for the math preview webview.
 *
 * The previous implementation depended on CDN-hosted KaTeX assets, which made
 * the panel hard to test offline. This version keeps the preview deterministic
 * and self-contained so extension tests can verify it without network access.
 */
export function buildMathPreviewHtml(latex: string, source: string): string {
    const hasContent = Boolean(latex || source);
    const escapedLatex = escapeForHtml(latex);
    const escapedSource = escapeForHtml(source);
    const renderedPreview = source ? simpleToUnicode(source) : '';
    const escapedRenderedPreview = escapeForHtml(renderedPreview);

    return `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta http-equiv="Content-Security-Policy"
          content="default-src 'none';
                   style-src 'unsafe-inline';
                   script-src 'none';
                   font-src 'none';">
    <title>Math Preview</title>
    <style>
        body {
            font-family: var(--vscode-font-family);
            font-size: var(--vscode-font-size);
            color: var(--vscode-foreground);
            background-color: var(--vscode-editor-background);
            margin: 0;
            padding: 16px;
        }

        h2 {
            font-size: 14px;
            font-weight: 600;
            margin: 0 0 12px 0;
            color: var(--vscode-foreground);
            border-bottom: 1px solid var(--vscode-panel-border);
            padding-bottom: 8px;
        }

        .empty-state {
            text-align: center;
            color: var(--vscode-descriptionForeground);
            font-style: italic;
            padding: 40px 16px;
        }

        .section {
            margin-bottom: 24px;
        }

        .section-label {
            font-size: 11px;
            font-weight: 600;
            text-transform: uppercase;
            letter-spacing: 0.5px;
            color: var(--vscode-descriptionForeground);
            margin-bottom: 8px;
        }

        #math-rendered {
            background-color: var(--vscode-editor-inactiveSelectionBackground);
            border-radius: 4px;
            padding: 16px;
            text-align: center;
            min-height: 40px;
            display: flex;
            flex-direction: column;
            align-items: center;
            justify-content: center;
            gap: 8px;
            overflow-x: auto;
        }

        .math-unicode {
            font-size: 1.4em;
            font-weight: 600;
            line-height: 1.5;
        }

        .math-latex {
            font-family: var(--vscode-editor-font-family);
            font-size: var(--vscode-editor-font-size);
            color: var(--vscode-descriptionForeground);
            white-space: pre-wrap;
            word-break: break-all;
        }

        .source-block {
            background-color: var(--vscode-textBlockQuote-background);
            border-radius: 4px;
            padding: 12px;
            font-family: var(--vscode-editor-font-family);
            font-size: var(--vscode-editor-font-size);
            white-space: pre-wrap;
            word-break: break-all;
            border-left: 3px solid var(--vscode-textLink-foreground);
        }
    </style>
</head>
<body>
    <h2>Math Preview</h2>

    ${!hasContent ? `
    <div class="empty-state">
        Move the cursor to a <code>m{ }</code> math block to see a preview.
    </div>
    ` : `
    <div class="section">
        <div class="section-label">Rendered</div>
        <div id="math-rendered">
            <div class="math-unicode">${escapedRenderedPreview || '&#8212;'}</div>
            ${escapedLatex ? `<div class="math-latex">${escapedLatex}</div>` : ''}
        </div>
    </div>

    <div class="section">
        <div class="section-label">Source</div>
        <div class="source-block">${escapedSource}</div>
    </div>
    `}
</body>
</html>`;
}

export class MathPreviewPanel implements vscode.Disposable {
    public static currentPanel: MathPreviewPanel | undefined;

    private readonly panel: vscode.WebviewPanel;
    private readonly decorationProvider: MathDecorationProvider;
    private disposables: vscode.Disposable[] = [];

    /** Currently displayed math content (to avoid redundant updates) */
    private currentContent: string | null = null;

    private constructor(
        panel: vscode.WebviewPanel,
        decorationProvider: MathDecorationProvider
    ) {
        this.panel = panel;
        this.decorationProvider = decorationProvider;

        // Set initial HTML
        this.panel.webview.html = this.getHtmlContent('', '');

        // Listen for cursor changes to update preview
        this.disposables.push(
            vscode.window.onDidChangeTextEditorSelection((event) => {
                this.handleSelectionChange(event);
            })
        );

        // Listen for active editor changes
        this.disposables.push(
            vscode.window.onDidChangeActiveTextEditor((editor) => {
                if (editor) {
                    this.updateForEditor(editor);
                }
            })
        );

        // Clean up on close
        this.panel.onDidDispose(() => this.dispose(), null, this.disposables);

        // Update for current editor immediately
        const editor = vscode.window.activeTextEditor;
        if (editor) {
            this.updateForEditor(editor);
        }
    }

    /**
     * Show or create the math preview panel.
     */
    public static show(decorationProvider: MathDecorationProvider): void {
        const column = vscode.window.activeTextEditor
            ? vscode.window.activeTextEditor.viewColumn
            : undefined;

        // If we already have a panel, reveal it
        if (MathPreviewPanel.currentPanel) {
            MathPreviewPanel.currentPanel.panel.reveal(
                column ? column + 1 : vscode.ViewColumn.Beside
            );
            return;
        }

        // Create new panel
        const panel = vscode.window.createWebviewPanel(
            'simpleMathPreview',
            'Math Preview',
            {
                viewColumn: vscode.ViewColumn.Beside,
                preserveFocus: true,
            },
            {
                enableScripts: true,
                retainContextWhenHidden: true,
            }
        );

        MathPreviewPanel.currentPanel = new MathPreviewPanel(panel, decorationProvider);
    }

    /**
     * Check if the panel is currently visible.
     */
    public static isVisible(): boolean {
        return MathPreviewPanel.currentPanel !== undefined;
    }

    /**
     * Close the preview panel if open.
     */
    public static close(): void {
        if (MathPreviewPanel.currentPanel) {
            MathPreviewPanel.currentPanel.panel.dispose();
        }
    }

    /**
     * Handle cursor selection changes.
     */
    private handleSelectionChange(event: vscode.TextEditorSelectionChangeEvent): void {
        this.updateForEditor(event.textEditor);
    }

    /**
     * Update the preview panel for the current editor position.
     */
    private updateForEditor(editor: vscode.TextEditor): void {
        if (editor.document.languageId !== 'simple') {
            return;
        }

        const cursorPos = editor.selection.active;
        const mathBlocks = this.decorationProvider.detectMathBlocks(editor.document);

        // Find the math block the cursor is inside or on
        let foundBlock: { content: string; source: string } | null = null;
        for (const block of mathBlocks) {
            if (block.fullRange.contains(cursorPos)) {
                foundBlock = {
                    content: block.content,
                    source: editor.document.getText(block.fullRange),
                };
                break;
            }
        }

        if (foundBlock) {
            // Only update if content changed
            if (foundBlock.content !== this.currentContent) {
                this.currentContent = foundBlock.content;
                const latex = this.toLatex(foundBlock.content);
                this.panel.webview.html = this.getHtmlContent(latex, foundBlock.source);
            }
        } else {
            if (this.currentContent !== null) {
                this.currentContent = null;
                this.panel.webview.html = this.getHtmlContent('', '');
            }
        }
    }

    /**
     * Convert math block content to LaTeX string.
     *
     * Mirrors src/lib/math_repr.spl render_latex_raw() for local preview.
     * Handles: ^N -> ^{N}, Greek names -> \alpha, sqrt(x) -> \sqrt{x},
     * frac(a,b) -> \frac{a}{b}, known functions -> \sin/\cos/etc.
     * See mathConverter.ts simpleToLatex() for the full conversion logic.
     */
    private toLatex(mathContent: string): string {
        return simpleToLatex(mathContent);
    }

    /**
     * Generate the full HTML content for the webview.
     * Uses an offline-safe preview so tests do not depend on network assets.
     */
    private getHtmlContent(latex: string, source: string): string {
        return buildMathPreviewHtml(latex, source);
    }

    /**
     * Dispose of all resources.
     */
    public dispose(): void {
        MathPreviewPanel.currentPanel = undefined;
        this.panel.dispose();

        for (const disposable of this.disposables) {
            disposable.dispose();
        }
        this.disposables = [];
    }
}
