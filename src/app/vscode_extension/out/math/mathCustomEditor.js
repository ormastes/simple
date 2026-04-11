"use strict";
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
exports.MathCustomEditorProvider = void 0;
exports.detectMathBlocksInSource = detectMathBlocksInSource;
exports.findMathBlockAtOffset = findMathBlockAtOffset;
exports.buildMathCustomEditorState = buildMathCustomEditorState;
exports.buildMathCustomEditorHtml = buildMathCustomEditorHtml;
const crypto = __importStar(require("crypto"));
const vscode = __importStar(require("vscode"));
const katex_1 = __importDefault(require("katex"));
const mathConverter_1 = require("./mathConverter");
const MATH_BLOCK_REGEX = /\b(?<prefix>m|loss|nograd)\{([^}]*(?:\{[^}]*\}[^}]*)*)\}/gs;
function escapeForHtml(text) {
    return text
        .replace(/&/g, '&amp;')
        .replace(/</g, '&lt;')
        .replace(/>/g, '&gt;')
        .replace(/"/g, '&quot;')
        .replace(/'/g, '&#039;');
}
function renderKatex(latex) {
    try {
        return {
            html: katex_1.default.renderToString(latex, {
                displayMode: true,
                throwOnError: true,
                output: 'html',
                trust: false,
            }),
            statusKind: 'ok',
            statusMessage: 'Rendered active math block.',
        };
    }
    catch (error) {
        return {
            html: `<div class="render-fallback"><div class="katex-error">Could not render the active math block.</div><div class="preview-text">${escapeForHtml(latex)}</div></div>`,
            statusKind: 'error',
            statusMessage: error instanceof Error ? error.message : 'Could not render the active math block.',
        };
    }
}
const katexInlineCache = new Map();
/** Render KaTeX for inline widget display (not clamped — natural height). Cached by latex string. */
function renderKatexInline(latex) {
    const cached = katexInlineCache.get(latex);
    if (cached !== undefined)
        return cached;
    let html;
    try {
        html = katex_1.default.renderToString(latex, {
            displayMode: true,
            throwOnError: false,
            output: 'html',
            trust: false,
        });
    }
    catch {
        html = `<span style="color: var(--vscode-errorForeground)">[math error]</span>`;
    }
    katexInlineCache.set(latex, html);
    return html;
}
function detectMathBlocksInSource(text) {
    const blocks = [];
    MATH_BLOCK_REGEX.lastIndex = 0;
    let match;
    while ((match = MATH_BLOCK_REGEX.exec(text)) !== null) {
        const prefix = match.groups?.prefix ?? 'm';
        const blockType = prefix === 'loss' ? 'loss' :
            prefix === 'nograd' ? 'nograd' : 'math';
        const content = match[2].trim();
        const latex = (0, mathConverter_1.simpleToLatex)(content);
        const renderedHtml = renderKatexInline(latex);
        blocks.push({
            blockType,
            fullStart: match.index,
            fullEnd: match.index + match[0].length,
            prefixEnd: match.index + prefix.length + 1,
            content,
            prefix,
            renderedHtml,
        });
    }
    return blocks;
}
function findMathBlockAtOffset(text, offset) {
    const clippedOffset = Math.max(0, Math.min(text.length, offset));
    return detectMathBlocksInSource(text).find(block => clippedOffset >= block.fullStart && clippedOffset <= block.fullEnd);
}
function formatBlockLabel(blockType) {
    switch (blockType) {
        case 'loss':
            return 'loss{}';
        case 'nograd':
            return 'nograd{}';
        default:
            return 'm{}';
    }
}
function buildMathCustomEditorState(documentUri, sourceText, selectionStart, selectionEnd) {
    const clippedSelectionStart = Math.max(0, Math.min(sourceText.length, selectionStart));
    const clippedSelectionEnd = Math.max(clippedSelectionStart, Math.min(sourceText.length, selectionEnd));
    const block = findMathBlockAtOffset(sourceText, clippedSelectionStart);
    if (!block) {
        return {
            documentUri,
            sourceText,
            selectionStart: clippedSelectionStart,
            selectionEnd: clippedSelectionEnd,
            hasActiveBlock: false,
            activeBlockLabel: 'none',
            activeBlockSource: '',
            activeBlockPretty: '',
            activeBlockRenderedHtml: '',
            activeBlockStatusKind: 'info',
            activeBlockStatusMessage: 'Move the caret into a math block to render it.',
        };
    }
    const latex = (0, mathConverter_1.simpleToLatex)(block.content);
    const renderResult = renderKatex(latex);
    return {
        documentUri,
        sourceText,
        selectionStart: clippedSelectionStart,
        selectionEnd: clippedSelectionEnd,
        hasActiveBlock: true,
        activeBlockLabel: formatBlockLabel(block.blockType),
        activeBlockSource: block.content,
        activeBlockPretty: (0, mathConverter_1.simpleToUnicode)(block.content),
        activeBlockRenderedHtml: renderResult.html,
        activeBlockStatusKind: renderResult.statusKind,
        activeBlockStatusMessage: renderResult.statusMessage,
    };
}
function makeState(document, selectionStart, selectionEnd) {
    return buildMathCustomEditorState(document.uri.toString(), document.getText(), selectionStart, selectionEnd);
}
// ── HTML builder ─────────────────────────────────────────────────────
function buildMathCustomEditorHtml(katexCssUri, webviewJsUri, cspSource, nonce) {
    return `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta http-equiv="Content-Security-Policy"
          content="default-src 'none';
                   style-src ${cspSource} 'unsafe-inline';
                   font-src ${cspSource};
                   script-src ${cspSource} 'nonce-${nonce}';">
    <title>Simple Math Source Editor</title>
    <link rel="stylesheet" href="${katexCssUri}">
    <style nonce="${nonce}">
        * { box-sizing: border-box; }
        body {
            margin: 0;
            padding: 0;
            display: grid;
            grid-template-columns: minmax(0, 1.45fr) minmax(280px, 0.85fr);
            gap: 0;
            height: 100vh;
            background: var(--vscode-editor-background);
            color: var(--vscode-foreground);
            font-family: var(--vscode-font-family);
            font-size: var(--vscode-font-size);
            overflow: hidden;
        }

        /* ── Left panel: CodeMirror editor ── */
        #editor-panel {
            display: flex;
            flex-direction: column;
            min-height: 0;
            border-right: 1px solid var(--vscode-panel-border);
        }
        #editor-container {
            flex: 1;
            min-height: 0;
            overflow: hidden;
        }
        #editor-container .cm-editor {
            height: 100%;
        }
        #editor-container .cm-scroller {
            overflow: auto;
        }

        /* ── Right panel: Math preview ── */
        #preview-panel {
            display: flex;
            flex-direction: column;
            min-height: 0;
            overflow: hidden;
        }
        .panel-header {
            display: flex;
            justify-content: space-between;
            align-items: center;
            gap: 8px;
            padding: 10px 12px;
            border-bottom: 1px solid var(--vscode-panel-border);
            font-size: 12px;
            font-weight: 600;
            flex-shrink: 0;
        }
        .meta {
            color: var(--vscode-descriptionForeground);
            font-weight: 400;
            font-size: 11px;
        }
        .preview-body {
            padding: 12px;
            overflow: auto;
            flex: 1;
            min-height: 0;
            display: flex;
            flex-direction: column;
            gap: 12px;
        }
        .preview-block {
            border: 1px solid var(--vscode-panel-border);
            border-radius: 4px;
            padding: 10px;
            background: var(--vscode-editor-inactiveSelectionBackground);
        }
        .preview-label {
            font-size: 11px;
            text-transform: uppercase;
            letter-spacing: 0.4px;
            color: var(--vscode-descriptionForeground);
            margin-bottom: 6px;
        }
        .preview-text {
            white-space: pre-wrap;
            word-break: break-word;
        }

        /* ── Rendered math in preview — natural height ── */
        .preview-block .katex-display {
            margin: 0;
            padding: 0;
        }
        .preview-block .katex {
            font-size: 1.2em;
        }

        /* ── Status ── */
        .status {
            border-radius: 4px;
            padding: 8px 10px;
            font-size: 12px;
            line-height: 1.4;
            white-space: pre-wrap;
            word-break: break-word;
        }
        .status-info {
            background: var(--vscode-editor-inactiveSelectionBackground);
            color: var(--vscode-descriptionForeground);
        }
        .status-ok {
            background: color-mix(in srgb, var(--vscode-testing-iconPassed, #388a34) 18%, transparent);
            color: var(--vscode-testing-iconPassed, #388a34);
        }
        .status-error {
            background: color-mix(in srgb, var(--vscode-errorForeground, #f14c4c) 18%, transparent);
            color: var(--vscode-errorForeground, #f14c4c);
        }
        .empty-state {
            color: var(--vscode-descriptionForeground);
            font-style: italic;
        }
        .katex-error {
            color: var(--vscode-errorForeground);
            font-family: var(--vscode-editor-font-family);
        }
        .render-fallback {
            display: flex;
            flex-direction: column;
            gap: 8px;
        }
        button {
            background: var(--vscode-button-background);
            color: var(--vscode-button-foreground);
            border: 1px solid var(--vscode-button-border, transparent);
            padding: 6px 10px;
            border-radius: 4px;
            cursor: pointer;
            font-size: 11px;
        }
        button:hover {
            background: var(--vscode-button-hoverBackground);
        }
    </style>
</head>
<body>
    <section id="editor-panel">
        <div id="editor-container"></div>
    </section>

    <aside id="preview-panel">
        <div class="panel-header">
            <span>Math Preview</span>
            <div style="display: flex; gap: 6px; align-items: center;">
                <span class="meta" id="selection">0-0</span>
                <button type="button" id="refresh">Refresh</button>
            </div>
        </div>
        <div class="preview-body">
            <div class="preview-block">
                <div class="preview-label">Status</div>
                <div id="render-status" class="status status-info">Move the caret into a math block to render it.</div>
            </div>
            <div class="preview-block">
                <div class="preview-label">Active Block</div>
                <div class="preview-text" id="block-label">none</div>
            </div>
            <div class="preview-block">
                <div class="preview-label">Rendered</div>
                <div id="rendered"><div class="empty-state">Move the caret into a math block.</div></div>
            </div>
            <div class="preview-block">
                <div class="preview-label">Source</div>
                <div class="preview-text" id="block-source"><span class="empty-state">No active math block</span></div>
            </div>
            <div class="preview-block">
                <div class="preview-label">Pretty</div>
                <div class="preview-text" id="block-pretty"><span class="empty-state">No active math block</span></div>
            </div>
        </div>
    </aside>

    <script nonce="${nonce}">
        // acquireVsCodeApi() can only be called ONCE — store it globally
        var __vscodeApi = acquireVsCodeApi();
        document.getElementById('refresh').addEventListener('click', function() {
            __vscodeApi.postMessage({ type: 'requestSync' });
        });
    </script>
    <script nonce="${nonce}" src="${webviewJsUri}"></script>
    <script nonce="${nonce}">
        (function() {
            var container = document.getElementById('editor-container');
            try {
                if (typeof MathEditorWebview !== 'undefined') {
                    MathEditorWebview.boot(__vscodeApi);
                } else {
                    container.textContent = 'Error: webview bundle not loaded. Open Developer Tools for details.';
                    console.error('[math-editor] MathEditorWebview undefined after script load');
                }
            } catch (e) {
                container.textContent = 'Boot error: ' + e.message;
                console.error('[math-editor] boot error:', e);
            }
        })();
    </script>
</body>
</html>`;
}
// ── Provider ─────────────────────────────────────────────────────────
function fullDocumentRange(document) {
    const lastLine = document.lineCount > 0 ? document.lineAt(document.lineCount - 1) : undefined;
    const end = lastLine
        ? new vscode.Position(document.lineCount - 1, lastLine.text.length)
        : new vscode.Position(0, 0);
    return new vscode.Range(new vscode.Position(0, 0), end);
}
class MathCustomEditorProvider {
    constructor(extensionUri) {
        this.extensionUri = extensionUri;
    }
    async resolveCustomTextEditor(document, webviewPanel, _token) {
        const katexDistUri = vscode.Uri.joinPath(this.extensionUri, 'node_modules', 'katex', 'dist');
        const webviewOutUri = vscode.Uri.joinPath(this.extensionUri, 'out', 'webview');
        webviewPanel.webview.options = {
            enableScripts: true,
            localResourceRoots: [katexDistUri, webviewOutUri],
        };
        const katexCssUri = webviewPanel.webview.asWebviewUri(vscode.Uri.joinPath(katexDistUri, 'katex.min.css')).toString();
        const webviewJsUri = webviewPanel.webview.asWebviewUri(vscode.Uri.joinPath(webviewOutUri, 'mathEditor.js')).toString();
        const nonce = crypto.randomBytes(16).toString('base64');
        console.log('[math-editor] katexCssUri:', katexCssUri);
        console.log('[math-editor] webviewJsUri:', webviewJsUri);
        console.log('[math-editor] cspSource:', webviewPanel.webview.cspSource);
        console.log('[math-editor] localResourceRoots:', [katexDistUri.fsPath, webviewOutUri.fsPath]);
        let selectionStart = 0;
        let selectionEnd = 0;
        let isApplyingEdit = false;
        const postSync = async () => {
            const text = document.getText();
            const mathBlocks = detectMathBlocksInSource(text);
            await webviewPanel.webview.postMessage({
                type: 'sync',
                sourceText: text,
                selectionStart,
                selectionEnd,
                mathBlocks,
            });
        };
        const postFocusedBlock = async () => {
            const state = makeState(document, selectionStart, selectionEnd);
            await webviewPanel.webview.postMessage({
                type: 'focusedBlock',
                html: state.activeBlockRenderedHtml,
                label: state.activeBlockLabel,
                source: state.activeBlockSource,
                pretty: state.activeBlockPretty,
                statusKind: state.activeBlockStatusKind,
                statusMessage: state.activeBlockStatusMessage,
                hasContent: state.hasActiveBlock,
            });
        };
        // Set initial HTML
        webviewPanel.webview.html = buildMathCustomEditorHtml(katexCssUri, webviewJsUri, webviewPanel.webview.cspSource, nonce);
        const changeDocumentSubscription = vscode.workspace.onDidChangeTextDocument(event => {
            if (event.document.uri.toString() !== document.uri.toString() || isApplyingEdit) {
                return;
            }
            void postSync();
        });
        const messageSubscription = webviewPanel.webview.onDidReceiveMessage(async (message) => {
            if (message.type === 'ready' || message.type === 'requestSync') {
                await postSync();
                await postFocusedBlock();
                return;
            }
            if (message.type === 'selectionChanged') {
                selectionStart = message.selectionStart;
                selectionEnd = message.selectionEnd;
                await postFocusedBlock();
                return;
            }
            // editAll
            selectionStart = message.selectionStart;
            selectionEnd = message.selectionEnd;
            if (message.source === document.getText()) {
                await postFocusedBlock();
                return;
            }
            isApplyingEdit = true;
            try {
                const edit = new vscode.WorkspaceEdit();
                edit.replace(document.uri, fullDocumentRange(document), message.source);
                const applied = await vscode.workspace.applyEdit(edit);
                if (!applied) {
                    await webviewPanel.webview.postMessage({
                        type: 'error',
                        message: 'Failed to apply source edit to the backing document.',
                    });
                }
            }
            finally {
                isApplyingEdit = false;
            }
            await postFocusedBlock();
        });
        webviewPanel.onDidDispose(() => {
            changeDocumentSubscription.dispose();
            messageSubscription.dispose();
        });
    }
}
exports.MathCustomEditorProvider = MathCustomEditorProvider;
MathCustomEditorProvider.viewType = 'simple.mathSourceEditor';
//# sourceMappingURL=mathCustomEditor.js.map