"use strict";
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
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.MathDecorationProvider = void 0;
const vscode = __importStar(require("vscode"));
const mathConverter_1 = require("./mathConverter");
const mathSvgRenderer_1 = require("./mathSvgRenderer");
/** Indicator symbols shown when block delimiters are concealed.
 *  m{} has no indicator — it's the default math block.
 *  loss{} shows L, nograd{} shows ∅. */
const BLOCK_INDICATORS = {
    math: '', // no indicator for default math blocks
    loss: 'L', // Loss function
    nograd: '\u2205', // ∅ no-gradient
};
/**
 * Regex for detecting math-mode custom blocks: m{}, loss{}, nograd{}.
 * Handles one level of nested braces (e.g., m{ x^{2} + y^{2} }).
 * Uses the 's' (dotAll) flag so `.` matches newlines for multi-line blocks.
 * Named group `prefix` captures the block keyword for type detection.
 */
const MATH_BLOCK_REGEX = /\b(?<prefix>m|loss|nograd)\{([^}]*(?:\{[^}]*\}[^}]*)*)\}/gs;
class MathDecorationProvider {
    constructor() {
        this.disposables = [];
        this.isEnabled = true;
        /** Line numbers that the cursor currently occupies (used for reveal) */
        this.cursorLines = new Set();
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
        // Vertical alignment for non-math text on lines with SVG math (default: center)
        const alignment = vscode.workspace.getConfiguration('simple').get('math.alignment', 'center');
        const vertAlign = alignment === 'center' ? 'middle' : 'baseline';
        this.lineAlignDecorationType = vscode.window.createTextEditorDecorationType({
            textDecoration: `none; vertical-align: ${vertAlign}`,
        });
        // Listen for text changes
        this.disposables.push(vscode.workspace.onDidChangeTextDocument((event) => {
            const editor = vscode.window.activeTextEditor;
            if (editor && event.document === editor.document) {
                this.scheduleUpdate(editor);
            }
        }));
        // Listen for active editor changes
        this.disposables.push(vscode.window.onDidChangeActiveTextEditor((editor) => {
            if (editor) {
                this.scheduleUpdate(editor);
            }
        }));
        // Listen for cursor movement (cursor-aware reveal)
        this.disposables.push(vscode.window.onDidChangeTextEditorSelection((event) => {
            this.handleSelectionChange(event);
        }));
        // Listen for configuration changes
        this.disposables.push(vscode.workspace.onDidChangeConfiguration((event) => {
            if (event.affectsConfiguration('simple.math.renderInline') ||
                event.affectsConfiguration('simple.math.alignment')) {
                const config = vscode.workspace.getConfiguration('simple');
                this.isEnabled = config.get('math.renderInline', true);
                // Recreate alignment decoration type if alignment changed
                if (event.affectsConfiguration('simple.math.alignment')) {
                    this.lineAlignDecorationType.dispose();
                    const align = config.get('math.alignment', 'center');
                    const va = align === 'center' ? 'middle' : 'baseline';
                    this.lineAlignDecorationType = vscode.window.createTextEditorDecorationType({
                        textDecoration: `none; vertical-align: ${va}`,
                    });
                }
                const editor = vscode.window.activeTextEditor;
                if (editor) {
                    this.updateDecorations(editor);
                }
            }
        }));
        // Apply to current editor on activation
        const editor = vscode.window.activeTextEditor;
        if (editor) {
            this.updateDecorations(editor);
        }
    }
    /**
     * Toggle inline rendering on or off.
     */
    setEnabled(enabled) {
        this.isEnabled = enabled;
        const editor = vscode.window.activeTextEditor;
        if (editor) {
            this.updateDecorations(editor);
        }
    }
    /**
     * Get current enabled state.
     */
    getEnabled() {
        return this.isEnabled;
    }
    /**
     * Set the SVG cache directory for rendered math images.
     * When set, decorations use SVG rendering instead of Unicode text.
     */
    setSvgCacheDir(dir) {
        this.svgCacheDir = dir;
    }
    /**
     * Handle cursor/selection changes for cursor-aware reveal.
     * When the cursor is on a math block line, decorations are removed
     * so the user sees the raw source. When the cursor leaves, decorations
     * are re-applied.
     */
    handleSelectionChange(event) {
        const editor = event.textEditor;
        if (editor.document.languageId !== 'simple') {
            return;
        }
        // Collect all line numbers the cursor currently occupies
        const newCursorLines = new Set();
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
    scheduleUpdate(editor) {
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
    getForegroundColor() {
        const kind = vscode.window.activeColorTheme.kind;
        // Light themes use dark text, dark themes use light text
        return kind === vscode.ColorThemeKind.Light || kind === vscode.ColorThemeKind.HighContrastLight
            ? '#333333' : '#cccccc';
    }
    /**
     * Update all decorations for the given editor.
     */
    updateDecorations(editor) {
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
        const contentDecorations = [];
        const openDecorations = [];
        const closeDecorations = [];
        const svgDecorations = [];
        const lineAlignDecorations = [];
        const fg = this.getForegroundColor();
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
            let svgUri;
            if (this.svgCacheDir) {
                const latex = (0, mathConverter_1.simpleToLatex)(block.content);
                svgUri = (0, mathSvgRenderer_1.renderToSvgFile)(latex, this.svgCacheDir, fg);
            }
            if (svgUri) {
                // SVG view mode: hide full block, show SVG icon before
                // Prefix with block indicator if not empty (loss→L, nograd→∅, math→nothing)
                const indicatorPrefix = indicator ? `${indicator} ` : '';
                svgDecorations.push({
                    range: block.fullRange,
                    hoverMessage: new vscode.MarkdownString(`**${label} Block**\n\n\`${block.content}\`\n\n_Rendered:_ ${rendered}\n\n$$${(0, mathConverter_1.simpleToLatex)(block.content)}$$`),
                    renderOptions: {
                        before: {
                            contentIconPath: svgUri,
                            // Pull the SVG upward so the fraction bar aligns with text center.
                            // margin-bottom negative shifts the icon up relative to baseline.
                            margin: '0 4px -0.6em 0',
                            textDecoration: 'none; vertical-align: middle',
                        },
                    },
                });
                // Apply vertical alignment to the non-math text before the block
                const lineStart = new vscode.Position(block.fullRange.start.line, 0);
                if (block.fullRange.start.character > 0) {
                    lineAlignDecorations.push({
                        range: new vscode.Range(lineStart, block.fullRange.start),
                    });
                }
            }
            else {
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
        editor.setDecorations(this.lineAlignDecorationType, lineAlignDecorations);
    }
    /**
     * Detect all math-mode custom blocks (m{}, loss{}, nograd{}) in a document.
     */
    detectMathBlocks(document) {
        const text = document.getText();
        const blocks = [];
        MATH_BLOCK_REGEX.lastIndex = 0;
        let match;
        while ((match = MATH_BLOCK_REGEX.exec(text)) !== null) {
            const prefix = match.groups.prefix;
            const prefixLen = prefix.length + 1; // prefix + `{`
            const blockType = prefix === 'loss' ? 'loss' :
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
    renderMathBlock(content) {
        return (0, mathConverter_1.simpleToUnicode)(content);
    }
    /**
     * Check if any line of a math block overlaps with the current cursor lines.
     */
    isBlockOnCursorLine(block) {
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
    setsEqual(a, b) {
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
    dispose() {
        if (this.debounceTimer) {
            clearTimeout(this.debounceTimer);
        }
        this.contentDecorationType.dispose();
        this.openDelimiterDecorationType.dispose();
        this.closeDelimiterDecorationType.dispose();
        this.svgViewDecorationType.dispose();
        this.lineAlignDecorationType.dispose();
        for (const disposable of this.disposables) {
            disposable.dispose();
        }
        this.disposables = [];
    }
}
exports.MathDecorationProvider = MathDecorationProvider;
//# sourceMappingURL=mathDecorationProvider.js.map