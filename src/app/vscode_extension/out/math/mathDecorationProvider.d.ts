/**
 * Math Block Decoration Provider
 *
 * Detects `m{ ... }` math blocks in Simple source files and applies
 * text decorations for visual rendering:
 * - Highlights math block content with a distinctive color
 * - Hides `m{` and `}` delimiters via opacity styling
 * - Shows rendered Unicode preview via before.contentText
 * - Cursor-aware reveal: removes decorations when cursor is on a math block line
 *
 * Rendering infrastructure:
 * - Local preview: Uses mathConverter.ts simpleToUnicode() for quick inline decoration.
 *   This mirrors src/lib/math_repr.spl to_pretty() in TypeScript for local rendering.
 * - Full rendering: The LSP hover handler (src/app/lsp/handlers/hover.spl) provides
 *   complete math rendering via render_latex_raw() and to_pretty() from the Simple
 *   runtime. See also src/lib/mathjax.spl for MathJax SVG/HTML rendering.
 */
import * as vscode from 'vscode';
/** Represents a detected math block range in the document */
interface MathBlockRange {
    /** Full range covering m{ ... } including delimiters */
    fullRange: vscode.Range;
    /** Range of just the opening `m{` delimiter */
    openRange: vscode.Range;
    /** Range of just the closing `}` delimiter */
    closeRange: vscode.Range;
    /** Range of the inner math content (between delimiters) */
    contentRange: vscode.Range;
    /** The raw math content string (trimmed) */
    content: string;
}
export declare class MathDecorationProvider implements vscode.Disposable {
    /** Decoration for the math content itself */
    private contentDecorationType;
    /** Decoration to hide the opening `m{` delimiter */
    private openDelimiterDecorationType;
    /** Decoration to hide the closing `}` delimiter */
    private closeDelimiterDecorationType;
    private disposables;
    private debounceTimer;
    private isEnabled;
    /** Line numbers that the cursor currently occupies (used for reveal) */
    private cursorLines;
    constructor();
    /**
     * Toggle inline rendering on or off.
     */
    setEnabled(enabled: boolean): void;
    /**
     * Get current enabled state.
     */
    getEnabled(): boolean;
    /**
     * Handle cursor/selection changes for cursor-aware reveal.
     * When the cursor is on a math block line, decorations are removed
     * so the user sees the raw source. When the cursor leaves, decorations
     * are re-applied.
     */
    private handleSelectionChange;
    /**
     * Schedule a debounced decoration update (300ms).
     */
    private scheduleUpdate;
    /**
     * Update all decorations for the given editor.
     */
    private updateDecorations;
    /**
     * Detect all m{ ... } math blocks in a document.
     */
    detectMathBlocks(document: vscode.TextDocument): MathBlockRange[];
    /**
     * Render a math block content string to Unicode pretty text.
     *
     * Uses the local TypeScript converter (mathConverter.ts) for quick inline
     * preview. This mirrors what to_pretty() does in src/lib/math_repr.spl
     * but runs locally in TypeScript without requiring the LSP server.
     *
     * For full rendering, the LSP hover handler (src/app/lsp/handlers/hover.spl)
     * returns rendered math via render_latex_raw() and to_pretty().
     */
    private renderMathBlock;
    /**
     * Check if any line of a math block overlaps with the current cursor lines.
     */
    private isBlockOnCursorLine;
    /**
     * Compare two sets for equality.
     */
    private setsEqual;
    /**
     * Dispose of all resources.
     */
    dispose(): void;
}
export {};
