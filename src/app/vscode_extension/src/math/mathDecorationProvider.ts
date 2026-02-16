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
 *   This mirrors src/std/math_repr.spl to_pretty() in TypeScript for local rendering.
 * - Full rendering: The LSP hover handler (src/app/lsp/handlers/hover.spl) provides
 *   complete math rendering via render_latex_raw() and to_pretty() from the Simple
 *   runtime. See also src/std/mathjax.spl for MathJax SVG/HTML rendering.
 */

import * as vscode from 'vscode';
import { simpleToUnicode } from './mathConverter';

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

/**
 * Regex for detecting m{ ... } math blocks.
 * Handles one level of nested braces (e.g., m{ x^{2} + y^{2} }).
 * Uses the 's' (dotAll) flag so `.` matches newlines for multi-line blocks.
 */
const MATH_BLOCK_REGEX = /m\{([^}]*(?:\{[^}]*\}[^}]*)*)\}/gs;

export class MathDecorationProvider implements vscode.Disposable {
    /** Decoration for the math content itself */
    private contentDecorationType: vscode.TextEditorDecorationType;
    /** Decoration to hide the opening `m{` delimiter */
    private openDelimiterDecorationType: vscode.TextEditorDecorationType;
    /** Decoration to hide the closing `}` delimiter */
    private closeDelimiterDecorationType: vscode.TextEditorDecorationType;

    private disposables: vscode.Disposable[] = [];
    private debounceTimer: ReturnType<typeof setTimeout> | undefined;
    private isEnabled: boolean = true;

    /** Line numbers that the cursor currently occupies (used for reveal) */
    private cursorLines: Set<number> = new Set();

    constructor() {
        // Create decoration types once and reuse them
        this.contentDecorationType = vscode.window.createTextEditorDecorationType({
            backgroundColor: new vscode.ThemeColor('editor.findMatchHighlightBackground'),
            borderRadius: '3px',
            border: '1px solid',
            borderColor: new vscode.ThemeColor('editorBracketMatch.border'),
        });

        this.openDelimiterDecorationType = vscode.window.createTextEditorDecorationType({
            opacity: '0',
            before: {
                contentText: '\u2202',  // mathematical partial derivative symbol as indicator
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
                if (event.affectsConfiguration('simple.math.renderInline')) {
                    const config = vscode.workspace.getConfiguration('simple');
                    this.isEnabled = config.get<boolean>('math.renderInline', true);
                    const editor = vscode.window.activeTextEditor;
                    if (editor) {
                        this.updateDecorations(editor);
                    }
                }
            })
        );

        // Apply to current editor on activation
        const editor = vscode.window.activeTextEditor;
        if (editor) {
            this.updateDecorations(editor);
        }
    }

    /**
     * Toggle inline rendering on or off.
     */
    public setEnabled(enabled: boolean): void {
        this.isEnabled = enabled;
        const editor = vscode.window.activeTextEditor;
        if (editor) {
            this.updateDecorations(editor);
        }
    }

    /**
     * Get current enabled state.
     */
    public getEnabled(): boolean {
        return this.isEnabled;
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
            return;
        }

        const mathBlocks = this.detectMathBlocks(editor.document);

        const contentDecorations: vscode.DecorationOptions[] = [];
        const openDecorations: vscode.DecorationOptions[] = [];
        const closeDecorations: vscode.DecorationOptions[] = [];

        for (const block of mathBlocks) {
            // Check if cursor is on any line of this math block -- if so, skip
            // decorations so the user can see the raw source
            if (this.isBlockOnCursorLine(block)) {
                continue;
            }

            const rendered = this.renderMathBlock(block.content);

            // Content decoration with hover message showing rendered Unicode
            contentDecorations.push({
                range: block.contentRange,
                hoverMessage: new vscode.MarkdownString(`**Math Block**\n\n\`${block.content}\`\n\n_Rendered:_ ${rendered}`),
            });

            // Hide opening delimiter and show rendered Unicode preview
            openDecorations.push({
                range: block.openRange,
                renderOptions: {
                    before: {
                        contentText: rendered,
                        color: new vscode.ThemeColor('editorLineNumber.foreground'),
                        fontStyle: 'normal',
                        margin: '0 2px 0 0',
                    },
                },
            });

            // Hide closing delimiter
            closeDecorations.push({
                range: block.closeRange,
            });
        }

        editor.setDecorations(this.contentDecorationType, contentDecorations);
        editor.setDecorations(this.openDelimiterDecorationType, openDecorations);
        editor.setDecorations(this.closeDelimiterDecorationType, closeDecorations);
    }

    /**
     * Detect all m{ ... } math blocks in a document.
     */
    public detectMathBlocks(document: vscode.TextDocument): MathBlockRange[] {
        const text = document.getText();
        const blocks: MathBlockRange[] = [];

        MATH_BLOCK_REGEX.lastIndex = 0;
        let match: RegExpExecArray | null;

        while ((match = MATH_BLOCK_REGEX.exec(text)) !== null) {
            const fullStart = document.positionAt(match.index);
            const fullEnd = document.positionAt(match.index + match[0].length);

            // `m{` is 2 characters
            const openStart = fullStart;
            const openEnd = document.positionAt(match.index + 2);

            // `}` is last character
            const closeStart = document.positionAt(match.index + match[0].length - 1);
            const closeEnd = fullEnd;

            // Content is between `m{` and `}`
            const contentStart = openEnd;
            const contentEnd = closeStart;

            const content = match[1].trim();

            blocks.push({
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
     * preview. This mirrors what to_pretty() does in src/std/math_repr.spl
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
        for (const disposable of this.disposables) {
            disposable.dispose();
        }
        this.disposables = [];
    }
}
