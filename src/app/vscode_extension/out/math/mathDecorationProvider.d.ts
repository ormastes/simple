/**
 * Math-Mode Block Decoration Provider
 *
 * Detects math-mode custom blocks (`m{}`, `loss{}`, `nograd{}`) in Simple
 * source files and applies text decorations for visual rendering:
 * - Highlights block content with a distinctive color
 * - Hides delimiters (`m{`, `loss{`, `nograd{`, `}`) via opacity styling
 * - Shows rendered Unicode preview with block-type indicator (∂/ℒ/∅)
 * - Cursor-aware reveal: removes decorations when cursor is on a block line
 *
 * Rendering infrastructure:
 * - Local preview: Uses mathConverter.ts simpleToUnicode() for quick inline decoration.
 *   This mirrors src/lib/math_repr.spl to_pretty() in TypeScript for local rendering.
 * - Full rendering: The LSP hover handler (src/app/lsp/handlers/hover.spl) provides
 *   complete math rendering via render_latex_raw() and to_pretty() from the Simple
 *   runtime. See also src/lib/mathjax.spl for MathJax SVG/HTML rendering.
 */
import * as vscode from 'vscode';
import { SvgRenderResult } from './mathSvgRenderer';
/** Block type for math-mode custom blocks */
type MathBlockType = 'math' | 'loss' | 'nograd';
/** Represents a detected math-mode block range in the document */
export interface MathBlockRange {
    /** Block type: math (m{}), loss (loss{}), or nograd (nograd{}) */
    blockType: MathBlockType;
    /** Full range covering the block including delimiters */
    fullRange: vscode.Range;
    /** Range of just the opening delimiter (e.g. `m{`, `loss{`) */
    openRange: vscode.Range;
    /** Range of just the closing `}` delimiter */
    closeRange: vscode.Range;
    /** Range of the inner math content (between delimiters) */
    contentRange: vscode.Range;
    /** The raw math content string (trimmed) */
    content: string;
}
export interface SvgDecorationLayout {
    height: string;
    width: string;
    spacerHeight: string;
    verticalAlign: string;
    boostApplied: boolean;
    layoutScale: number;
    debugMessage: string;
}
export declare function formatSvgDecorationLayoutLog(content: string, layout: SvgDecorationLayout): string;
export declare function buildSvgDecorationLayout(content: string, svgResult: SvgRenderResult, alignment: string): SvgDecorationLayout;
export declare class MathDecorationProvider implements vscode.Disposable {
    /** Decoration for the math content itself */
    private contentDecorationType;
    /** Decoration to hide the opening `m{` delimiter */
    private openDelimiterDecorationType;
    /** Decoration to hide the closing `}` delimiter */
    private closeDelimiterDecorationType;
    /** Decoration to hide the full math block and show SVG inline */
    private svgViewDecorationType;
    private disposables;
    private debounceTimer;
    private isEnabled;
    /** SVG cache directory for rendered math images */
    private svgCacheDir;
    /** When enabled, logs math SVG layout metrics for debugging decoration sizing */
    private debugLayout;
    private readonly debugLogger?;
    /** Line numbers that the cursor currently occupies (used for reveal) */
    private cursorLines;
    constructor(debugLogger?: (message: string) => void);
    /**
     * Toggle inline rendering on or off.
     */
    setEnabled(enabled: boolean): void;
    /**
     * Get current enabled state.
     */
    getEnabled(): boolean;
    /**
     * Set the SVG cache directory for rendered math images.
     * When set, decorations use SVG rendering instead of Unicode text.
     */
    setSvgCacheDir(dir: string): void;
    /**
     * Update decorations on the active text editor, if any.
     */
    private updateActiveEditor;
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
     * Try to get the editor foreground color for SVG rendering.
     */
    private getForegroundColor;
    /**
     * Update all decorations for the given editor.
     */
    private updateDecorations;
    /**
     * Detect all math-mode custom blocks (m{}, loss{}, nograd{}) in a document.
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
