"use strict";
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
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.MathPreviewPanel = void 0;
exports.buildMathPreviewHtml = buildMathPreviewHtml;
const vscode = __importStar(require("vscode"));
const katex_1 = __importDefault(require("katex"));
const mathConverter_1 = require("./mathConverter");
/**
 * Escape a string for safe embedding in HTML.
 */
function escapeForHtml(text) {
    return text
        .replace(/&/g, '&amp;')
        .replace(/</g, '&lt;')
        .replace(/>/g, '&gt;')
        .replace(/"/g, '&quot;')
        .replace(/'/g, '&#039;');
}
/**
 * Render a LaTeX string to HTML using KaTeX (server-side, no browser needed).
 * Falls back to escaped plain text if KaTeX fails to parse.
 */
function renderKatex(latex) {
    try {
        return katex_1.default.renderToString(latex, {
            displayMode: true,
            throwOnError: false,
            output: 'html',
            trust: false,
        });
    }
    catch {
        return `<span class="katex-error">${escapeForHtml(latex)}</span>`;
    }
}
/**
 * Generate HTML content for the math preview webview with KaTeX rendering.
 *
 * Uses bundled KaTeX CSS and fonts served as webview resources — fully offline-safe.
 * The `katexCssUri` parameter is a webview URI pointing to the bundled katex.min.css.
 * When called without a URI (e.g. in tests), falls back to inline Unicode preview.
 */
function buildMathPreviewHtml(latex, source, katexCssUri, cspSource) {
    const hasContent = Boolean(latex || source);
    const escapedSource = escapeForHtml(source);
    const katexHtml = latex ? renderKatex(latex) : '';
    const unicodeFallback = source ? escapeForHtml((0, mathConverter_1.simpleToUnicode)(source)) : '';
    // Use KaTeX CSS if URI provided, otherwise no external styles
    const katexStyleLink = katexCssUri
        ? `<link rel="stylesheet" href="${katexCssUri}">`
        : '';
    // CSP: allow KaTeX styles from extension resources, inline styles, and KaTeX fonts
    const resourceSource = cspSource ?? "'none'";
    const fontSrc = katexCssUri ? resourceSource : "'none'";
    const styleSrc = katexCssUri ? `${resourceSource} 'unsafe-inline'` : "'unsafe-inline'";
    return `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta http-equiv="Content-Security-Policy"
          content="default-src 'none';
                   style-src ${styleSrc};
                   font-src ${fontSrc};
                   script-src 'none';">
    <title>Math Preview</title>
    ${katexStyleLink}
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
            font-size: 1.1em;
            color: var(--vscode-descriptionForeground);
            margin-top: 4px;
        }

        .katex-error {
            font-family: var(--vscode-editor-font-family);
            color: var(--vscode-errorForeground);
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
            ${katexHtml || `<div class="math-unicode">${unicodeFallback || '&#8212;'}</div>`}
            ${katexHtml ? `<div class="math-unicode">${unicodeFallback}</div>` : ''}
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
class MathPreviewPanel {
    constructor(panel, decorationProvider, extensionUri) {
        this.disposables = [];
        /** Currently displayed math content (to avoid redundant updates) */
        this.currentContent = null;
        this.panel = panel;
        this.decorationProvider = decorationProvider;
        this.extensionUri = extensionUri;
        // Set initial HTML
        this.panel.webview.html = this.getHtmlContent('', '');
        // Listen for cursor changes to update preview
        this.disposables.push(vscode.window.onDidChangeTextEditorSelection((event) => {
            this.handleSelectionChange(event);
        }));
        // Listen for active editor changes
        this.disposables.push(vscode.window.onDidChangeActiveTextEditor((editor) => {
            if (editor) {
                this.updateForEditor(editor);
            }
        }));
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
    static show(decorationProvider, extensionUri) {
        const column = vscode.window.activeTextEditor
            ? vscode.window.activeTextEditor.viewColumn
            : undefined;
        // If we already have a panel, reveal it
        if (MathPreviewPanel.currentPanel) {
            MathPreviewPanel.currentPanel.panel.reveal(column ? column + 1 : vscode.ViewColumn.Beside);
            return;
        }
        // Allow webview to load KaTeX CSS and fonts from node_modules
        const katexDistUri = vscode.Uri.joinPath(extensionUri, 'node_modules', 'katex', 'dist');
        // Create new panel
        const panel = vscode.window.createWebviewPanel('simpleMathPreview', 'Math Preview', {
            viewColumn: vscode.ViewColumn.Beside,
            preserveFocus: true,
        }, {
            enableScripts: false,
            retainContextWhenHidden: true,
            localResourceRoots: [katexDistUri],
        });
        MathPreviewPanel.currentPanel = new MathPreviewPanel(panel, decorationProvider, extensionUri);
    }
    /**
     * Check if the panel is currently visible.
     */
    static isVisible() {
        return MathPreviewPanel.currentPanel !== undefined;
    }
    /**
     * Close the preview panel if open.
     */
    static close() {
        if (MathPreviewPanel.currentPanel) {
            MathPreviewPanel.currentPanel.panel.dispose();
        }
    }
    /**
     * Handle cursor selection changes.
     */
    handleSelectionChange(event) {
        this.updateForEditor(event.textEditor);
    }
    /**
     * Update the preview panel for the current editor position.
     */
    updateForEditor(editor) {
        if (editor.document.languageId !== 'simple') {
            return;
        }
        const cursorPos = editor.selection.active;
        const mathBlocks = this.decorationProvider.detectMathBlocks(editor.document);
        // Find the math block the cursor is inside or on
        let foundBlock = null;
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
        }
        else {
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
    toLatex(mathContent) {
        return (0, mathConverter_1.simpleToLatex)(mathContent);
    }
    /**
     * Get the webview URI for the bundled KaTeX CSS file.
     */
    getKatexCssUri() {
        const katexCssPath = vscode.Uri.joinPath(this.extensionUri, 'node_modules', 'katex', 'dist', 'katex.min.css');
        return this.panel.webview.asWebviewUri(katexCssPath).toString();
    }
    /**
     * Generate the full HTML content for the webview.
     * Uses bundled KaTeX for high-quality math rendering (offline-safe).
     */
    getHtmlContent(latex, source) {
        return buildMathPreviewHtml(latex, source, this.getKatexCssUri(), this.panel.webview.cspSource);
    }
    /**
     * Dispose of all resources.
     */
    dispose() {
        MathPreviewPanel.currentPanel = undefined;
        this.panel.dispose();
        for (const disposable of this.disposables) {
            disposable.dispose();
        }
        this.disposables = [];
    }
}
exports.MathPreviewPanel = MathPreviewPanel;
//# sourceMappingURL=mathPreviewPanel.js.map