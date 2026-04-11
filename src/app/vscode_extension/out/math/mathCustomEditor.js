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
exports.buildMathCustomEditorState = buildMathCustomEditorState;
exports.detectMathBlocksInSource = detectMathBlocksInSource;
exports.findMathBlockAtOffset = findMathBlockAtOffset;
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
function emptyState(documentUri, sourceText, selectionStart, selectionEnd) {
    return {
        documentUri,
        sourceText,
        selectionStart,
        selectionEnd,
        hasActiveBlock: false,
        activeBlockLabel: 'none',
        activeBlockSource: '',
        activeBlockPretty: '',
        activeBlockRenderedHtml: '',
        activeBlockStatusKind: 'info',
        activeBlockStatusMessage: 'Move the caret into a math block to render it.',
    };
}
function buildMathCustomEditorState(documentUri, sourceText, selectionStart, selectionEnd) {
    const clippedSelectionStart = Math.max(0, Math.min(sourceText.length, selectionStart));
    const clippedSelectionEnd = Math.max(clippedSelectionStart, Math.min(sourceText.length, selectionEnd));
    const block = findMathBlockAtOffset(sourceText, clippedSelectionStart);
    if (!block) {
        return emptyState(documentUri, sourceText, clippedSelectionStart, clippedSelectionEnd);
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
function statusClassName(kind) {
    switch (kind) {
        case 'error':
            return 'status status-error';
        case 'ok':
            return 'status status-ok';
        default:
            return 'status status-info';
    }
}
function escapeAttribute(value) {
    return escapeForHtml(value);
}
function renderStatusMessage(state) {
    return escapeForHtml(state.activeBlockStatusMessage);
}
function renderStatusClass(state) {
    return escapeAttribute(statusClassName(state.activeBlockStatusKind));
}
function renderStatusKind(kind) {
    return kind;
}
function dataStatusKind(state) {
    return escapeAttribute(renderStatusKind(state.activeBlockStatusKind));
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
function detectMathBlocksInSource(text) {
    const blocks = [];
    MATH_BLOCK_REGEX.lastIndex = 0;
    let match;
    while ((match = MATH_BLOCK_REGEX.exec(text)) !== null) {
        const prefix = match.groups?.prefix ?? 'm';
        const blockType = prefix === 'loss' ? 'loss' :
            prefix === 'nograd' ? 'nograd' : 'math';
        blocks.push({
            blockType,
            fullStart: match.index,
            fullEnd: match.index + match[0].length,
            content: match[2].trim(),
        });
    }
    return blocks;
}
function findMathBlockAtOffset(text, offset) {
    const clippedOffset = Math.max(0, Math.min(text.length, offset));
    return detectMathBlocksInSource(text).find(block => clippedOffset >= block.fullStart && clippedOffset <= block.fullEnd);
}
function buildMathCustomEditorHtml(state, katexCssUri, cspSource) {
    const nonce = crypto.randomBytes(16).toString('base64');
    const katexStyleLink = katexCssUri ? `<link rel="stylesheet" href="${katexCssUri}">` : '';
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
                   script-src 'nonce-${nonce}';">
    <title>Simple Math Source Editor</title>
    ${katexStyleLink}
    <style nonce="${nonce}">
        body {
            margin: 0;
            padding: 12px;
            display: grid;
            grid-template-columns: minmax(0, 1.45fr) minmax(280px, 0.85fr);
            gap: 12px;
            height: 100vh;
            box-sizing: border-box;
            background: var(--vscode-editor-background);
            color: var(--vscode-foreground);
            font-family: var(--vscode-font-family);
            font-size: var(--vscode-font-size);
        }
        .panel {
            display: flex;
            flex-direction: column;
            min-height: 0;
            border: 1px solid var(--vscode-panel-border);
            border-radius: 6px;
            background: var(--vscode-sideBar-background);
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
        }
        .meta {
            color: var(--vscode-descriptionForeground);
            font-weight: 400;
            font-size: 11px;
        }
        #source {
            flex: 1;
            width: 100%;
            min-height: 0;
            box-sizing: border-box;
            border: 0;
            outline: none;
            resize: none;
            padding: 12px;
            background: var(--vscode-editor-background);
            color: var(--vscode-editor-foreground);
            font-family: var(--vscode-editor-font-family);
            font-size: var(--vscode-editor-font-size);
            line-height: 1.5;
            tab-size: 4;
        }
        .preview-body {
            padding: 12px;
            overflow: auto;
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
        }
        button:hover {
            background: var(--vscode-button-hoverBackground);
        }
    </style>
</head>
<body>
    <section class="panel">
        <div class="panel-header">
            <span>Source</span>
            <span class="meta" id="doc-uri">${escapeForHtml(state.documentUri)}</span>
        </div>
        <textarea id="source" spellcheck="false">${escapeForHtml(state.sourceText)}</textarea>
    </section>

    <aside class="panel">
        <div class="panel-header">
            <span>Math Preview</span>
            <div><button type="button" id="refresh">Refresh</button></div>
        </div>
        <div class="preview-body">
            <div class="meta">Selection: <span id="selection">${state.selectionStart}-${state.selectionEnd}</span></div>
            <div class="preview-block">
                <div class="preview-label">Status</div>
                <div id="render-status" class="${renderStatusClass(state)}" data-kind="${dataStatusKind(state)}">${renderStatusMessage(state)}</div>
            </div>
            <div class="preview-block">
                <div class="preview-label">Active Block</div>
                <div class="preview-text" id="block-label">${escapeForHtml(state.activeBlockLabel)}</div>
            </div>
            <div class="preview-block">
                <div class="preview-label">Rendered</div>
                <div id="rendered">${state.hasActiveBlock ? state.activeBlockRenderedHtml : '<div class="empty-state">Move the caret into a math block.</div>'}</div>
            </div>
            <div class="preview-block">
                <div class="preview-label">Source</div>
                <div class="preview-text" id="block-source">${state.hasActiveBlock ? escapeForHtml(state.activeBlockSource) : '<span class="empty-state">No active math block</span>'}</div>
            </div>
            <div class="preview-block">
                <div class="preview-label">Pretty</div>
                <div class="preview-text" id="block-pretty">${state.hasActiveBlock ? escapeForHtml(state.activeBlockPretty) : '<span class="empty-state">No active math block</span>'}</div>
            </div>
        </div>
    </aside>

    <script nonce="${nonce}">
        const vscode = acquireVsCodeApi();
        const source = document.getElementById('source');
        const rendered = document.getElementById('rendered');
        const blockLabel = document.getElementById('block-label');
        const blockSource = document.getElementById('block-source');
        const blockPretty = document.getElementById('block-pretty');
        const renderStatus = document.getElementById('render-status');
        const selection = document.getElementById('selection');
        const docUri = document.getElementById('doc-uri');
        const refresh = document.getElementById('refresh');
        let editTimer = null;
        let isApplyingSync = false;

        function statusClass(kind) {
            switch (kind) {
                case 'error':
                    return 'status status-error';
                case 'ok':
                    return 'status status-ok';
                default:
                    return 'status status-info';
            }
        }

        function postSelection() {
            if (isApplyingSync) {
                return;
            }
            vscode.postMessage({
                type: 'selectionChanged',
                selectionStart: source.selectionStart ?? 0,
                selectionEnd: source.selectionEnd ?? 0,
            });
        }

        function scheduleEdit() {
            if (editTimer) {
                clearTimeout(editTimer);
            }
            editTimer = setTimeout(() => {
                vscode.postMessage({
                    type: 'editAll',
                    source: source.value,
                    selectionStart: source.selectionStart ?? 0,
                    selectionEnd: source.selectionEnd ?? 0,
                });
            }, 120);
        }

        source.addEventListener('input', scheduleEdit);
        source.addEventListener('click', postSelection);
        source.addEventListener('keyup', postSelection);
        source.addEventListener('select', postSelection);
        refresh.addEventListener('click', () => vscode.postMessage({ type: 'requestSync' }));

        window.addEventListener('message', (event) => {
            const msg = event.data;
            if (msg.type === 'sync') {
                const state = msg.state;
                isApplyingSync = true;
                try {
                    docUri.textContent = state.documentUri;
                    selection.textContent = state.selectionStart + '-' + state.selectionEnd;
                    if (source.value !== state.sourceText) {
                        source.value = state.sourceText;
                    }
                    if (typeof source.setSelectionRange === 'function') {
                        source.setSelectionRange(state.selectionStart, state.selectionEnd);
                    }
                    renderStatus.className = statusClass(state.activeBlockStatusKind);
                    renderStatus.dataset.kind = state.activeBlockStatusKind;
                    renderStatus.textContent = state.activeBlockStatusMessage;
                    blockLabel.textContent = state.activeBlockLabel;
                    if (state.hasActiveBlock) {
                        rendered.innerHTML = state.activeBlockRenderedHtml;
                        blockSource.textContent = state.activeBlockSource;
                        blockPretty.textContent = state.activeBlockPretty;
                    } else {
                        rendered.innerHTML = '<div class="empty-state">Move the caret into a math block.</div>';
                        blockSource.innerHTML = '<span class="empty-state">No active math block</span>';
                        blockPretty.innerHTML = '<span class="empty-state">No active math block</span>';
                    }
                } finally {
                    isApplyingSync = false;
                }
            } else if (msg.type === 'error') {
                rendered.innerHTML = '<div class="empty-state">' + msg.message + '</div>';
            }
        });

        vscode.postMessage({ type: 'ready' });
    </script>
</body>
</html>`;
}
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
        const katexCssUri = webviewPanel.webview.asWebviewUri(vscode.Uri.joinPath(katexDistUri, 'katex.min.css')).toString();
        webviewPanel.webview.options = {
            enableScripts: true,
            localResourceRoots: [katexDistUri],
        };
        let selectionStart = 0;
        let selectionEnd = 0;
        let isApplyingEdit = false;
        const postState = async () => {
            await webviewPanel.webview.postMessage({
                type: 'sync',
                state: makeState(document, selectionStart, selectionEnd),
            });
        };
        webviewPanel.webview.html = buildMathCustomEditorHtml(makeState(document, selectionStart, selectionEnd), katexCssUri, webviewPanel.webview.cspSource);
        const changeDocumentSubscription = vscode.workspace.onDidChangeTextDocument(event => {
            if (event.document.uri.toString() !== document.uri.toString() || isApplyingEdit) {
                return;
            }
            void postState();
        });
        const messageSubscription = webviewPanel.webview.onDidReceiveMessage(async (message) => {
            if (message.type === 'ready' || message.type === 'requestSync') {
                await postState();
                return;
            }
            if (message.type === 'selectionChanged') {
                selectionStart = message.selectionStart;
                selectionEnd = message.selectionEnd;
                await postState();
                return;
            }
            selectionStart = message.selectionStart;
            selectionEnd = message.selectionEnd;
            if (message.source === document.getText()) {
                await postState();
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
            await postState();
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