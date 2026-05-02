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
import { simpleToLatex, simpleToUnicode } from './mathConverter';
import { renderToSvgFile, SvgRenderResult } from './mathSvgRenderer';

/** Block type for math-mode custom blocks */
type MathBlockType = 'math' | 'loss' | 'nograd';

/** Indicator symbols shown when block delimiters are concealed.
 *  m{} has no indicator — it's the default math block.
 *  loss{} shows L, nograd{} shows ∅. */
const BLOCK_INDICATORS: Record<MathBlockType, string> = {
    math: '',          // no indicator for default math blocks
    loss: 'L',         // Loss function
    nograd: '\u2205',  // ∅ no-gradient
};

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
    verticalAlign: string;
    fitApplied: boolean;
    inlineScale: number;
    debugMessage: string;
}

export function formatSvgDecorationLayoutLog(content: string, layout: SvgDecorationLayout): string {
    return `[simple.math.layout] eq="${content}" height=${layout.height} width=${layout.width} fit=${layout.fitApplied ? 'yes' : 'no'} scale=${layout.inlineScale.toFixed(2)} align=${layout.verticalAlign}`;
}

// HEIGHT FIT PATH:
// These constants control the inline SVG box that VS Code decorations render.
// They do NOT change editor row height. They only size the math image itself.
const MAX_INLINE_HEIGHT_EM = 3.0;
const MIN_INLINE_HEIGHT_EM = 0.92;
const MIN_INLINE_WIDTH_EM = 0.75;

export function buildSvgDecorationLayout(
    content: string,
    svgResult: SvgRenderResult,
    alignment: string,
): SvgDecorationLayout {
    // HEIGHT FIT PATH:
    // This is the only place where inline math height is decided.
    // Tall equations are scaled down to fit inside a normal editor line box.
    const inlineScale = Math.min(1.0, MAX_INLINE_HEIGHT_EM / Math.max(svgResult.heightEm, 0.01));
    const fitApplied = inlineScale < 0.999;
    const heightEm = Math.max(svgResult.heightEm * inlineScale, MIN_INLINE_HEIGHT_EM);
    const widthEm = Math.max(svgResult.widthEm * inlineScale, MIN_INLINE_WIDTH_EM);
    // HEIGHT FIT PATH:
    // Alignment only adjusts where the fitted SVG sits in the line.
    // It does not request a larger line height from VS Code.
    const verticalAlign = alignment === 'center'
        ? 'middle'
        : `-${(svgResult.descentEm * inlineScale).toFixed(2)}em`;

    return {
        height: `${heightEm.toFixed(2)}em`,
        width: `${widthEm.toFixed(2)}em`,
        verticalAlign,
        fitApplied,
        inlineScale,
        debugMessage: JSON.stringify({
            content,
            fitApplied,
            inlineScale,
            sourceHeightEm: Number(svgResult.heightEm.toFixed(3)),
            sourceWidthEm: Number(svgResult.widthEm.toFixed(3)),
            heightEm: Number(heightEm.toFixed(3)),
            widthEm: Number(widthEm.toFixed(3)),
            descentEm: Number((svgResult.descentEm * inlineScale).toFixed(3)),
            verticalAlign,
            alignment,
        }),
    };
}

/**
 * Regex for detecting math-mode custom blocks: m{}, loss{}, nograd{}.
 * Handles one level of nested braces (e.g., m{ x^{2} + y^{2} }).
 * Uses the 's' (dotAll) flag so `.` matches newlines for multi-line blocks.
 * Named group `prefix` captures the block keyword for type detection.
 */
const MATH_BLOCK_REGEX = /\b(?<prefix>m|loss|nograd)\{([^}]*(?:\{[^}]*\}[^}]*)*)\}/gs;

export class MathDecorationProvider implements vscode.Disposable {
    /** Decoration for the math content itself */
    private contentDecorationType: vscode.TextEditorDecorationType;
    /** Decoration to hide the opening `m{` delimiter */
    private openDelimiterDecorationType: vscode.TextEditorDecorationType;
    /** Decoration to hide the closing `}` delimiter */
    private closeDelimiterDecorationType: vscode.TextEditorDecorationType;
    /** Decoration to hide the full math block and show SVG inline */
    private svgViewDecorationType: vscode.TextEditorDecorationType;

    private disposables: vscode.Disposable[] = [];
    private debounceTimer: ReturnType<typeof setTimeout> | undefined;
    private isEnabled: boolean = true;

    /** SVG cache directory for rendered math images */
    private svgCacheDir: string | undefined;

    /** When enabled, logs math SVG layout metrics for debugging decoration sizing */
    private debugLayout: boolean = false;
    private readonly debugLogger?: (message: string) => void;

    /** Line numbers that the cursor currently occupies (used for reveal) */
    private cursorLines: Set<number> = new Set();

    constructor(debugLogger?: (message: string) => void) {
        this.debugLogger = debugLogger;
        // Create decoration types once and reuse them
        this.contentDecorationType = vscode.window.createTextEditorDecorationType({
            backgroundColor: new vscode.ThemeColor('editor.findMatchHighlightBackground'),
            borderRadius: '3px',
            border: '1px solid',
            borderColor: new vscode.ThemeColor('editorBracketMatch.border'),
        });

        this.openDelimiterDecorationType = vscode.window.createTextEditorDecorationType({
            opacity: '0',
            // Default before text is overridden per-block via renderOptions
            before: {
                contentText: '',
                color: new vscode.ThemeColor('editorLineNumber.foreground'),
                fontStyle: 'normal',
                margin: '0 2px 0 0',
            },
        });

        this.closeDelimiterDecorationType = vscode.window.createTextEditorDecorationType({
            opacity: '0',
            after: {
                contentText: '',
            },
        });

        // SVG view mode: hide entire math block, show rendered SVG via before icon
        this.svgViewDecorationType = vscode.window.createTextEditorDecorationType({
            opacity: '0',
            textDecoration: 'none; font-size: 0.001em; letter-spacing: -9999px',
        });

        // Listen for text changes
        this.disposables.push(
            vscode.workspace.onDidChangeTextDocument((event) => {
                const editor = vscode.window.activeTextEditor;
                if (editor && event.document === editor.document) {
                    this.scheduleUpdate(editor);
                }
            })
        );

        // Listen for active editor changes
        this.disposables.push(
            vscode.window.onDidChangeActiveTextEditor((editor) => {
                if (editor) {
                    this.scheduleUpdate(editor);
                }
            })
        );

        // Listen for cursor movement (cursor-aware reveal)
        this.disposables.push(
            vscode.window.onDidChangeTextEditorSelection((event) => {
                this.handleSelectionChange(event);
            })
        );

        // Listen for configuration changes
        this.disposables.push(
            vscode.workspace.onDidChangeConfiguration((event) => {
                if (event.affectsConfiguration('simple.math.renderInline') ||
                    event.affectsConfiguration('simple.math.alignment') ||
                    event.affectsConfiguration('simple.math.debugLayout')) {
                    const config = vscode.workspace.getConfiguration('simple');
                    this.isEnabled = config.get<boolean>('math.renderInline', true);
                    this.debugLayout = config.get<boolean>('math.debugLayout', false);
                    this.updateActiveEditor();
                }
            })
        );

        // Apply to current editor on activation
        this.updateActiveEditor();
    }

    /**
     * Toggle inline rendering on or off.
     */
    public setEnabled(enabled: boolean): void {
        this.isEnabled = enabled;
        this.updateActiveEditor();
    }

    /**
     * Get current enabled state.
     */
    public getEnabled(): boolean {
        return this.isEnabled;
    }

    /**
     * Set the SVG cache directory for rendered math images.
     * When set, decorations use SVG rendering instead of Unicode text.
     */
    public setSvgCacheDir(dir: string): void {
        this.svgCacheDir = dir;
    }

    /**
     * Update decorations on the active text editor, if any.
     */
    private updateActiveEditor(): void {
        const editor = vscode.window.activeTextEditor;
        if (editor) {
            this.updateDecorations(editor);
        }
    }

    /**
     * Handle cursor/selection changes for cursor-aware reveal.
     * When the cursor is on a math block line, decorations are removed
     * so the user sees the raw source. When the cursor leaves, decorations
     * are re-applied.
     */
    private handleSelectionChange(event: vscode.TextEditorSelectionChangeEvent): void {
        const editor = event.textEditor;
        if (editor.document.languageId !== 'simple') {
            return;
        }

        // Collect all line numbers the cursor currently occupies
        const newCursorLines = new Set<number>();
        for (const selection of event.selections) {
            for (let line = selection.start.line; line <= selection.end.line; line++) {
                newCursorLines.add(line);
            }
        }

        // If cursor lines changed, re-apply decorations
        if (!this.setsEqual(this.cursorLines, newCursorLines)) {
            this.cursorLines = newCursorLines;
            this.scheduleUpdate(editor);
        }
    }

    /**
     * Schedule a debounced decoration update (300ms).
     */
    private scheduleUpdate(editor: vscode.TextEditor): void {
        if (this.debounceTimer) {
            clearTimeout(this.debounceTimer);
        }
        this.debounceTimer = setTimeout(() => {
            this.updateDecorations(editor);
        }, 300);
    }

    /**
     * Try to get the editor foreground color for SVG rendering.
     */
    private getForegroundColor(): string {
        const kind = vscode.window.activeColorTheme.kind;
        // Light themes use dark text, dark themes use light text
        return kind === vscode.ColorThemeKind.Light || kind === vscode.ColorThemeKind.HighContrastLight
            ? '#333333' : '#cccccc';
    }

    /**
     * Update all decorations for the given editor.
     */
    private updateDecorations(editor: vscode.TextEditor): void {
        if (editor.document.languageId !== 'simple') {
            return;
        }

        // If disabled, clear all decorations
        if (!this.isEnabled) {
            editor.setDecorations(this.contentDecorationType, []);
            editor.setDecorations(this.openDelimiterDecorationType, []);
            editor.setDecorations(this.closeDelimiterDecorationType, []);
            editor.setDecorations(this.svgViewDecorationType, []);
            return;
        }

        const mathBlocks = this.detectMathBlocks(editor.document);
        const contentDecorations: vscode.DecorationOptions[] = [];
        const openDecorations: vscode.DecorationOptions[] = [];
        const closeDecorations: vscode.DecorationOptions[] = [];
        const svgDecorations: vscode.DecorationOptions[] = [];

        const fg = this.getForegroundColor();
        const config = vscode.workspace.getConfiguration('simple');
        const alignment = config.get<string>('math.alignment', 'center');
        this.debugLayout = config.get<boolean>('math.debugLayout', false);

        for (const block of mathBlocks) {
            // Check if cursor is on any line of this math block -- if so, skip
            // decorations so the user can see the raw source
            if (this.isBlockOnCursorLine(block)) {
                continue;
            }

            const rendered = this.renderMathBlock(block.content);
            const indicator = BLOCK_INDICATORS[block.blockType];
            const label = block.blockType === 'math' ? 'Math' :
                          block.blockType === 'loss' ? 'Loss' : 'NoGrad';

            // Try SVG rendering if cache dir is available
            let svgResult: SvgRenderResult | undefined;
            if (this.svgCacheDir) {
                const latex = simpleToLatex(block.content);
                svgResult = renderToSvgFile(latex, this.svgCacheDir, fg);
            }

            if (svgResult) {
                const layout = buildSvgDecorationLayout(block.content, svgResult, alignment);
                if (this.debugLayout) {
                    const message = formatSvgDecorationLayoutLog(block.content, layout);
                    console.log(message);
                    this.debugLogger?.(message);
                }

                svgDecorations.push({
                    range: block.fullRange,
                    hoverMessage: new vscode.MarkdownString(
                        `**${label} Block**\n\n\`${block.content}\`\n\n_Rendered:_ ${rendered}\n\n$$${simpleToLatex(block.content)}$$`
                    ),
                    renderOptions: {
                        before: {
                            contentIconPath: svgResult.uri,
                            margin: '0 4px 0 0',
                            // HEIGHT FIT PATH:
                            // These width/height values size the rendered math SVG.
                            // They are the runtime values to inspect when debugging sizing.
                            width: layout.width,
                            height: layout.height,
                            textDecoration: `none; vertical-align: ${layout.verticalAlign}`,
                        },
                    },
                });
            } else {
                // Fallback: Unicode text mode (no SVG)
                // Build display text: indicator + rendered (no indicator for m{})
                const displayText = indicator
                    ? `${indicator} ${rendered}`
                    : rendered;

                contentDecorations.push({
                    range: block.contentRange,
                    hoverMessage: new vscode.MarkdownString(`**${label} Block**\n\n\`${block.content}\`\n\n_Rendered:_ ${rendered}`),
                });

                openDecorations.push({
                    range: block.openRange,
                    renderOptions: {
                        before: {
                            contentText: displayText,
                            color: new vscode.ThemeColor('editorLineNumber.foreground'),
                            fontStyle: 'normal',
                            margin: '0 2px 0 0',
                        },
                    },
                });

                closeDecorations.push({
                    range: block.closeRange,
                });
            }
        }

        editor.setDecorations(this.contentDecorationType, contentDecorations);
        editor.setDecorations(this.openDelimiterDecorationType, openDecorations);
        editor.setDecorations(this.closeDelimiterDecorationType, closeDecorations);
        editor.setDecorations(this.svgViewDecorationType, svgDecorations);
    }

    /**
     * Detect all math-mode custom blocks (m{}, loss{}, nograd{}) in a document.
     */
    public detectMathBlocks(document: vscode.TextDocument): MathBlockRange[] {
        const text = document.getText();
        const blocks: MathBlockRange[] = [];

        MATH_BLOCK_REGEX.lastIndex = 0;
        let match: RegExpExecArray | null;

        while ((match = MATH_BLOCK_REGEX.exec(text)) !== null) {
            const prefix = match.groups!.prefix;
            const prefixLen = prefix.length + 1; // prefix + `{`
            const blockType: MathBlockType =
                prefix === 'loss' ? 'loss' :
                prefix === 'nograd' ? 'nograd' : 'math';

            const fullStart = document.positionAt(match.index);
            const fullEnd = document.positionAt(match.index + match[0].length);

            // Opening delimiter: prefix + `{`
            const openStart = fullStart;
            const openEnd = document.positionAt(match.index + prefixLen);

            // `}` is last character
            const closeStart = document.positionAt(match.index + match[0].length - 1);
            const closeEnd = fullEnd;

            // Content is between opening delimiter and `}`
            const contentStart = openEnd;
            const contentEnd = closeStart;

            const content = match[2].trim();

            blocks.push({
                blockType,
                fullRange: new vscode.Range(fullStart, fullEnd),
                openRange: new vscode.Range(openStart, openEnd),
                closeRange: new vscode.Range(closeStart, closeEnd),
                contentRange: new vscode.Range(contentStart, contentEnd),
                content,
            });
        }

        return blocks;
    }

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
    private renderMathBlock(content: string): string {
        return simpleToUnicode(content);
    }

    /**
     * Check if any line of a math block overlaps with the current cursor lines.
     */
    private isBlockOnCursorLine(block: MathBlockRange): boolean {
        for (let line = block.fullRange.start.line; line <= block.fullRange.end.line; line++) {
            if (this.cursorLines.has(line)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Compare two sets for equality.
     */
    private setsEqual(a: Set<number>, b: Set<number>): boolean {
        if (a.size !== b.size) {
            return false;
        }
        for (const val of a) {
            if (!b.has(val)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Dispose of all resources.
     */
    public dispose(): void {
        if (this.debounceTimer) {
            clearTimeout(this.debounceTimer);
        }
        this.contentDecorationType.dispose();
        this.openDelimiterDecorationType.dispose();
        this.closeDelimiterDecorationType.dispose();
        this.svgViewDecorationType.dispose();
        for (const disposable of this.disposables) {
            disposable.dispose();
        }
        this.disposables = [];
    }
}
