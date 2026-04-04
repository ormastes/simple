/**
 * Math Preview Panel - Webview panel for LaTeX math preview
 *
 * Shows a side panel that renders LaTeX for the math block under the cursor.
 * Uses KaTeX (loaded from CDN) for rendering inside the webview.
 * Updates automatically when the cursor moves to a different math block.
 *
 * LaTeX conversion mirrors src/lib/math_repr.spl render_latex_raw() for local
 * preview. The full Simple rendering pipeline is:
 *   src/lib/math_repr.spl  - Parser + renderers (to_pretty, render_latex_raw, to_md)
 *   src/lib/mathjax.spl    - MathJax SFFI wrapper (SVG/HTML rendering via Node.js)
 *   src/app/lsp/handlers/hover.spl - LSP hover uses both for server-side rendering
 */
import * as vscode from 'vscode';
import { MathDecorationProvider } from './mathDecorationProvider';
export declare class MathPreviewPanel implements vscode.Disposable {
    static currentPanel: MathPreviewPanel | undefined;
    private readonly panel;
    private readonly decorationProvider;
    private disposables;
    /** Currently displayed math content (to avoid redundant updates) */
    private currentContent;
    private constructor();
    /**
     * Show or create the math preview panel.
     */
    static show(decorationProvider: MathDecorationProvider): void;
    /**
     * Check if the panel is currently visible.
     */
    static isVisible(): boolean;
    /**
     * Close the preview panel if open.
     */
    static close(): void;
    /**
     * Handle cursor selection changes.
     */
    private handleSelectionChange;
    /**
     * Update the preview panel for the current editor position.
     */
    private updateForEditor;
    /**
     * Convert math block content to LaTeX string.
     *
     * Mirrors src/lib/math_repr.spl render_latex_raw() for local preview.
     * Handles: ^N -> ^{N}, Greek names -> \alpha, sqrt(x) -> \sqrt{x},
     * frac(a,b) -> \frac{a}{b}, known functions -> \sin/\cos/etc.
     * See mathConverter.ts simpleToLatex() for the full conversion logic.
     */
    private toLatex;
    /**
     * Generate the full HTML content for the webview.
     * Uses KaTeX from CDN for rendering.
     */
    private getHtmlContent;
    /**
     * Escape a string for safe embedding in HTML.
     */
    private escapeForHtml;
    /**
     * Dispose of all resources.
     */
    dispose(): void;
}
