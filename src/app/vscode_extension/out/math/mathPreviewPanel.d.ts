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
/**
 * Generate offline-safe HTML content for the math preview webview.
 *
 * The previous implementation depended on CDN-hosted KaTeX assets, which made
 * the panel hard to test offline. This version keeps the preview deterministic
 * and self-contained so extension tests can verify it without network access.
 */
export declare function buildMathPreviewHtml(latex: string, source: string): string;
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
     * Uses an offline-safe preview so tests do not depend on network assets.
     */
    private getHtmlContent;
    /**
     * Dispose of all resources.
     */
    dispose(): void;
}
