"use strict";
/**
 * Math Sync Panel - webview companion that mirrors the active math block and
 * delegates edits back to the source document.
 *
 * The source editor remains canonical. This panel is a synchronized view with a
 * local source textarea, rendered preview, and edit delegation through normal
 * VS Code document edits so undo/redo and diagnostics stay owned by the editor.
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
exports.MathSyncPanel = void 0;
exports.findMathBlockAtPosition = findMathBlockAtPosition;
exports.replaceRangeInText = replaceRangeInText;
exports.buildMathSyncPanelHtml = buildMathSyncPanelHtml;
const crypto = __importStar(require("crypto"));
const vscode = __importStar(require("vscode"));
const katex_1 = __importDefault(require("katex"));
const mathConverter_1 = require("./mathConverter");
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
function findMathBlockAtPosition(provider, document, position) {
    return provider.detectMathBlocks(document).find(block => block.fullRange.contains(position));
}
function offsetAtText(text, position) {
    let line = 0;
    let column = 0;
    for (let i = 0; i < text.length; i++) {
        if (line === position.line && column === position.character) {
            return i;
        }
        if (text[i] === '\n') {
            line++;
            column = 0;
            continue;
        }
        column++;
    }
    return text.length;
}
function replaceRangeInText(text, range, replacement) {
    const start = Math.max(0, Math.min(text.length, offsetAtText(text, range.start)));
    const end = Math.max(start, Math.min(text.length, offsetAtText(text, range.end)));
    return `${text.slice(0, start)}${replacement}${text.slice(end)}`;
}
function buildMathSyncPanelHtml(state, katexCssUri) {
    const nonce = crypto.randomBytes(16).toString('base64');
    const sourceValue = escapeForHtml(state.blockText);
    const prettyValue = escapeForHtml(state.pretty);
    const katexStyleLink = katexCssUri ? `<link rel="stylesheet" href="${katexCssUri}">` : '';
    const fontSrc = katexCssUri ? `${katexCssUri.replace(/\/[^/]*$/, '/')}*` : "'none'";
    const styleSrc = katexCssUri ? `${katexCssUri} 'unsafe-inline'` : "'unsafe-inline'";
    return `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta http-equiv="Content-Security-Policy"
          content="default-src 'none';
                   style-src ${styleSrc};
                   font-src ${fontSrc};
                   script-src 'nonce-${nonce}';">
    <title>Math Sync Panel</title>
    ${katexStyleLink}
    <style nonce="${nonce}">
        body {
            font-family: var(--vscode-font-family);
            font-size: var(--vscode-font-size);
            color: var(--vscode-foreground);
            background-color: var(--vscode-editor-background);
            margin: 0;
            padding: 12px;
            display: flex;
            flex-direction: column;
            gap: 12px;
        }
        h2 {
            margin: 0;
            font-size: 14px;
            font-weight: 600;
            border-bottom: 1px solid var(--vscode-panel-border);
            padding-bottom: 8px;
        }
        .meta {
            font-size: 11px;
            color: var(--vscode-descriptionForeground);
            display: flex;
            gap: 12px;
            flex-wrap: wrap;
        }
        .grid {
            display: grid;
            grid-template-columns: 1fr;
            gap: 12px;
        }
        .section {
            border: 1px solid var(--vscode-panel-border);
            border-radius: 6px;
            padding: 12px;
            background: var(--vscode-sideBar-background);
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
            overflow-x: auto;
            min-height: 44px;
        }
        #math-source {
            width: 100%;
            min-height: 150px;
            resize: vertical;
            box-sizing: border-box;
            border-radius: 4px;
            border: 1px solid var(--vscode-panel-border);
            background: var(--vscode-editor-background);
            color: var(--vscode-editor-foreground);
            font-family: var(--vscode-editor-font-family);
            font-size: var(--vscode-editor-font-size);
            line-height: 1.45;
            padding: 10px;
        }
        .katex-error {
            color: var(--vscode-errorForeground);
            font-family: var(--vscode-editor-font-family);
        }
        .preview-row {
            display: flex;
            justify-content: space-between;
            align-items: center;
            gap: 8px;
        }
        .button-row {
            display: flex;
            gap: 8px;
            flex-wrap: wrap;
        }
        button {
            background: var(--vscode-button-background);
            color: var(--vscode-button-foreground);
            border: 1px solid var(--vscode-button-border, transparent);
            padding: 6px 10px;
            border-radius: 4px;
            cursor: pointer;
        }
        button:hover {
            background: var(--vscode-button-hoverBackground);
        }
        .empty-state {
            color: var(--vscode-descriptionForeground);
            font-style: italic;
        }
        .source-preview {
            font-size: 11px;
            color: var(--vscode-descriptionForeground);
            white-space: pre-wrap;
            word-break: break-word;
            margin-top: 8px;
        }
    </style>
</head>
<body>
    <h2>Math Sync Panel</h2>
    <div class="meta">
        <div>Document: <span id="doc-uri">${escapeForHtml(state.documentUri)}</span></div>
        <div>Selection: <span id="selection">${state.selectionStart}-${state.selectionEnd}</span></div>
        <div>Block: <span id="block-label">${escapeForHtml(state.blockLabel)}</span></div>
    </div>

    <div class="grid">
        <div class="section">
            <div class="preview-row">
                <div class="section-label">Rendered</div>
                <div class="button-row">
                    <button id="refresh-button" type="button">Refresh from Source</button>
                </div>
            </div>
            <div id="math-rendered">
                ${state.hasContent ? state.renderedHtml : `<div class="empty-state">Move the cursor onto a math block in the source editor.</div>`}
            </div>
            <div class="source-preview" id="pretty">${state.hasContent ? `Pretty: ${prettyValue}` : ''}</div>
        </div>

        <div class="section">
            <div class="section-label">Editable Source</div>
            <textarea id="math-source" spellcheck="false" placeholder="Math block source...">${sourceValue}</textarea>
            <div class="source-preview" id="source-preview">${state.hasContent ? `Source mirror: ${sourceValue}` : ''}</div>
        </div>
    </div>

    <script nonce="${nonce}">
        const vscode = acquireVsCodeApi();
        const source = document.getElementById('math-source');
        const rendered = document.getElementById('math-rendered');
        const pretty = document.getElementById('pretty');
        const selection = document.getElementById('selection');
        const blockLabel = document.getElementById('block-label');
        const docUri = document.getElementById('doc-uri');
        const sourcePreview = document.getElementById('source-preview');
        const refreshButton = document.getElementById('refresh-button');

        let timer = null;

        function sendEdit() {
            vscode.postMessage({ type: 'edit', source: source.value });
        }

        source.addEventListener('input', () => {
            if (timer) {
                clearTimeout(timer);
            }
            timer = setTimeout(sendEdit, 150);
        });

        refreshButton.addEventListener('click', () => {
            vscode.postMessage({ type: 'request-sync' });
        });

        window.addEventListener('message', (event) => {
            const msg = event.data;
            if (msg.type === 'sync') {
                const state = msg.state;
                docUri.textContent = state.documentUri;
                selection.textContent = state.selectionStart + '-' + state.selectionEnd;
                blockLabel.textContent = state.blockLabel;
                pretty.textContent = state.hasContent ? 'Pretty: ' + state.pretty : '';
                sourcePreview.textContent = state.hasContent ? 'Source mirror: ' + state.blockText : '';
                if (source.value !== state.blockText) {
                    source.value = state.blockText;
                }
                if (state.hasContent) {
                    rendered.innerHTML = state.renderedHtml;
                } else {
                    rendered.innerHTML = '<div class="empty-state">Move the cursor onto a math block in the source editor.</div>';
                }
            } else if (msg.type === 'empty') {
                rendered.innerHTML = '<div class="empty-state">' + msg.message + '</div>';
                pretty.textContent = '';
                sourcePreview.textContent = '';
                source.value = '';
            } else if (msg.type === 'error') {
                rendered.innerHTML = '<div class="empty-state">' + msg.message + '</div>';
            }
        });

        vscode.postMessage({ type: 'ready' });
    </script>
</body>
</html>`;
}
function makeState(document, uri, block, selection) {
    const latex = (0, mathConverter_1.simpleToLatex)(block.content);
    const pretty = (0, mathConverter_1.simpleToUnicode)(block.content);
    const renderedHtml = renderKatex(latex);
    const selectionStart = Math.max(0, document.offsetAt(selection.start) - document.offsetAt(block.contentRange.start));
    const selectionEnd = Math.max(selectionStart, document.offsetAt(selection.end) - document.offsetAt(block.contentRange.start));
    return {
        documentUri: uri.toString(),
        blockText: block.content,
        latex,
        pretty,
        renderedHtml,
        blockLabel: formatBlockLabel(block.blockType),
        selectionStart,
        selectionEnd,
        hasContent: true,
    };
}
class MathSyncPanel {
    constructor(panel, decorationProvider, extensionUri) {
        this.disposables = [];
        this.panel = panel;
        this.decorationProvider = decorationProvider;
        this.extensionUri = extensionUri;
        this.katexCssUri = this.panel.webview.asWebviewUri(vscode.Uri.joinPath(extensionUri, 'node_modules', 'katex', 'dist', 'katex.min.css')).toString();
        this.panel.webview.html = buildMathSyncPanelHtml({
            documentUri: '',
            blockText: '',
            latex: '',
            pretty: '',
            renderedHtml: '',
            blockLabel: 'none',
            selectionStart: 0,
            selectionEnd: 0,
            hasContent: false,
        }, this.katexCssUri);
        this.disposables.push(this.panel.webview.onDidReceiveMessage((message) => {
            void this.handleMessage(message);
        }));
        this.disposables.push(vscode.window.onDidChangeTextEditorSelection((event) => this.handleSelectionChange(event)));
        this.disposables.push(vscode.workspace.onDidChangeTextDocument((event) => this.handleDocumentChange(event)));
        this.panel.onDidDispose(() => this.dispose(), null, this.disposables);
        const editor = vscode.window.activeTextEditor;
        if (editor) {
            this.syncFromEditor(editor);
        }
    }
    static show(decorationProvider, extensionUri) {
        const column = vscode.window.activeTextEditor
            ? vscode.window.activeTextEditor.viewColumn
            : undefined;
        if (MathSyncPanel.currentPanel) {
            MathSyncPanel.currentPanel.panel.reveal(column ? column + 1 : vscode.ViewColumn.Beside);
            const editor = vscode.window.activeTextEditor;
            if (editor) {
                MathSyncPanel.currentPanel.syncFromEditor(editor);
            }
            return;
        }
        const katexDistUri = vscode.Uri.joinPath(extensionUri, 'node_modules', 'katex', 'dist');
        const panel = vscode.window.createWebviewPanel('simpleMathSyncPanel', 'Math Sync Panel', {
            viewColumn: vscode.ViewColumn.Beside,
            preserveFocus: true,
        }, {
            enableScripts: true,
            retainContextWhenHidden: true,
            localResourceRoots: [katexDistUri],
        });
        MathSyncPanel.currentPanel = new MathSyncPanel(panel, decorationProvider, extensionUri);
    }
    static isVisible() {
        return MathSyncPanel.currentPanel !== undefined;
    }
    static close() {
        if (MathSyncPanel.currentPanel) {
            MathSyncPanel.currentPanel.panel.dispose();
        }
    }
    async handleMessage(message) {
        if (message.type === 'ready') {
            const editor = vscode.window.activeTextEditor;
            if (editor) {
                this.syncFromEditor(editor);
            }
            return;
        }
        if (message.type === 'request-sync') {
            const editor = vscode.window.activeTextEditor;
            if (editor) {
                this.syncFromEditor(editor);
            }
            return;
        }
        if (message.type === 'edit') {
            const editor = this.getEditorForCurrentDocument();
            if (!editor || !this.currentDocumentUri) {
                return;
            }
            const block = this.getCurrentBlock(editor.document);
            if (!block) {
                return;
            }
            if (message.source === block.content) {
                return;
            }
            await editor.edit(editBuilder => {
                editBuilder.replace(block.contentRange, message.source);
            });
            this.syncFromEditor(editor);
        }
    }
    handleSelectionChange(event) {
        if (!this.currentDocumentUri || event.textEditor.document.uri.toString() !== this.currentDocumentUri.toString()) {
            return;
        }
        this.syncFromEditor(event.textEditor);
    }
    handleDocumentChange(event) {
        if (!this.currentDocumentUri || event.document.uri.toString() !== this.currentDocumentUri.toString()) {
            return;
        }
        const editor = this.getEditorForCurrentDocument();
        if (editor) {
            this.syncFromEditor(editor);
        }
    }
    getEditorForCurrentDocument() {
        if (!this.currentDocumentUri) {
            return vscode.window.activeTextEditor;
        }
        return vscode.window.visibleTextEditors.find(editor => editor.document.uri.toString() === this.currentDocumentUri?.toString()) ?? vscode.window.activeTextEditor;
    }
    getCurrentBlock(document) {
        const editor = vscode.window.visibleTextEditors.find(e => e.document.uri.toString() === document.uri.toString());
        const position = editor?.selection.active ?? new vscode.Position(0, 0);
        return findMathBlockAtPosition(this.decorationProvider, document, position);
    }
    syncFromEditor(editor) {
        if (editor.document.languageId !== 'simple') {
            return;
        }
        const block = this.getCurrentBlock(editor.document);
        this.currentDocumentUri = editor.document.uri;
        if (!block) {
            this.lastStateKey = undefined;
            this.panel.webview.postMessage({
                type: 'empty',
                message: 'Move the cursor onto a math block in the source editor.',
            });
            return;
        }
        const state = makeState(editor.document, editor.document.uri, block, editor.selection);
        const stateKey = JSON.stringify([
            state.documentUri,
            state.blockText,
            state.selectionStart,
            state.selectionEnd,
            state.blockLabel,
        ]);
        if (stateKey === this.lastStateKey) {
            return;
        }
        this.lastStateKey = stateKey;
        this.panel.webview.postMessage({
            type: 'sync',
            state,
        });
    }
    dispose() {
        MathSyncPanel.currentPanel = undefined;
        this.panel.dispose();
        for (const disposable of this.disposables) {
            disposable.dispose();
        }
        this.disposables = [];
    }
}
exports.MathSyncPanel = MathSyncPanel;
//# sourceMappingURL=mathSyncPanel.js.map