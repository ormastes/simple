"use strict";
/**
 * Rich Custom Editor Provider for Simple language files.
 *
 * Provides a CodeMirror 6-based webview editor with:
 * - Variable line heights (math/images expand lines naturally)
 * - Cursor-aware view mode (non-cursor blocks render as widgets)
 * - Image embedding via img{} blocks
 * - Bi-directional sync with VSCode TextDocument
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
exports.RichCustomEditorProvider = void 0;
const crypto = __importStar(require("crypto"));
const fs = __importStar(require("fs"));
const vscode = __importStar(require("vscode"));
const katex_1 = __importDefault(require("katex"));
const blockDetector_1 = require("./blockDetector");
const imageResolver_1 = require("./imageResolver");
const mathConverter_1 = require("./mathConverter");
const simpleSymbolProviders_1 = require("./symbols/simpleSymbolProviders");
const testDiscovery_1 = require("./testing/testDiscovery");
// ── Math rendering (KaTeX) ───────────────────────────────────────────
const katexCache = new Map();
function renderKatexInline(latex) {
    const cached = katexCache.get(latex);
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
        html = '<span style="color: var(--vscode-errorForeground)">[math error]</span>';
    }
    katexCache.set(latex, html);
    return html;
}
// ── Block rendering ──────────────────────────────────────────────────
function renderDetectedBlocks(blocks, documentUri, webview) {
    return blocks.map(block => {
        if (block.kind === 'img') {
            const parsed = (0, imageResolver_1.parseImageContent)(block.content);
            if (!parsed) {
                return {
                    ...block,
                    renderedHtml: '',
                    imageUri: undefined,
                    displayMode: 'block',
                    status: 'error',
                    errorMessage: 'Invalid image path',
                };
            }
            const uri = (0, imageResolver_1.resolveImageUri)(parsed.path, documentUri, webview);
            return {
                ...block,
                renderedHtml: '',
                imageUri: uri ?? undefined,
                displayMode: 'block',
                status: uri ? 'ok' : 'error',
                errorMessage: uri ? undefined : `Image not found: ${parsed.path}`,
            };
        }
        // Math/loss/nograd/graph — render via KaTeX
        const latex = (0, mathConverter_1.simpleToLatex)(block.content);
        const html = renderKatexInline(latex);
        return {
            ...block,
            renderedHtml: html,
            displayMode: 'inline',
            status: 'ok',
        };
    });
}
function getRichEditorSettings() {
    const config = vscode.workspace.getConfiguration('simple.richEditor');
    return {
        showBlockBorders: config.get('showBlockBorders', false),
        centerLineNumbers: config.get('centerLineNumbers', true),
    };
}
// ── HTML builder ─────────────────────────────────────────────────────
function buildRichEditorHtml(katexCssUri, richEditorBundleSource, cspSource, nonce) {
    return `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta http-equiv="Content-Security-Policy"
          content="default-src 'none';
                   style-src ${cspSource} 'unsafe-inline';
                   font-src ${cspSource};
                   img-src ${cspSource} data: https:;
                   script-src ${cspSource} 'nonce-${nonce}';">
    <title>Simple Rich Editor</title>
    <link rel="stylesheet" href="${katexCssUri}">
    <style nonce="${nonce}">
        * { box-sizing: border-box; }
        html, body {
            margin: 0; padding: 0;
            height: 100vh; width: 100vw;
            overflow: hidden;
            background: var(--vscode-editor-background);
            color: var(--vscode-foreground);
            font-family: var(--vscode-font-family);
        }
        #editor-container {
            height: 100%;
            width: 100%;
            overflow: auto;
            position: relative;
        }
        .boot-error {
            margin: 24px;
            padding: 16px 18px;
            border-radius: 10px;
            border: 1px solid color-mix(in srgb, var(--vscode-errorForeground) 30%, transparent);
            background: color-mix(in srgb, var(--vscode-errorForeground) 10%, transparent);
            color: var(--vscode-editor-foreground);
            line-height: 1.5;
        }
        .boot-error strong {
            display: block;
            margin-bottom: 8px;
            color: var(--vscode-errorForeground);
        }
        .boot-error code {
            font-family: var(--vscode-editor-font-family);
            font-size: 0.95em;
        }
    </style>
</head>
<body>
    <div id="editor-container"></div>
    <script nonce="${nonce}">
window.__simpleRichEditorBundleStage = 'inline-script-start';
window.addEventListener('error', (event) => {
    const detail = event?.error?.message || event?.message || 'unknown script error';
    window.__simpleRichEditorLastError = String(detail);
});
${richEditorBundleSource}
window.__simpleRichEditorBundleStage = 'bundle-finished';
    </script>
    <script nonce="${nonce}">
        (() => {
            const container = document.getElementById('editor-container');
            try {
                if (!globalThis.RichEditorWebview || typeof globalThis.RichEditorWebview.boot !== 'function') {
                    throw new Error('richEditor.js did not expose RichEditorWebview.boot()');
                }
                globalThis.RichEditorWebview.boot();
            } catch (error) {
                console.error('Simple Rich Editor boot failed', error);
                if (container) {
                    const message = error instanceof Error ? error.message : String(error);
                    const bundleStage = String(globalThis.__simpleRichEditorBundleStage ?? 'missing');
                    const lastError = String(globalThis.__simpleRichEditorLastError ?? 'none');
                    container.innerHTML =
                        '<div class="boot-error">' +
                        '<strong>Simple Rich Editor failed to start.</strong>' +
                        '<div>Check that the webview bundle exists and compiled successfully.</div>' +
                        '<div><code>' + message.replace(/</g, '&lt;') + '</code></div>' +
                        '<div><code>bundle stage: ' + bundleStage.replace(/</g, '&lt;') + '</code></div>' +
                        '<div><code>last error: ' + lastError.replace(/</g, '&lt;') + '</code></div>' +
                        '</div>';
                }
            }
        })();
    </script>
</body>
</html>`;
}
// ── Helper ───────────────────────────────────────────────────────────
function fullDocumentRange(document) {
    const lastLine = document.lineCount > 0 ? document.lineAt(document.lineCount - 1) : undefined;
    const end = lastLine
        ? new vscode.Position(document.lineCount - 1, lastLine.text.length)
        : new vscode.Position(0, 0);
    return new vscode.Range(new vscode.Position(0, 0), end);
}
function buildRichEditorSymbols(document) {
    return (0, simpleSymbolProviders_1.indexDocumentSymbols)(document).map((symbol) => ({
        name: symbol.name,
        kind: vscode.SymbolKind[symbol.kind],
        detail: symbol.detail,
        line: symbol.selectionRange.start.line,
        from: document.offsetAt(symbol.selectionRange.start),
        to: document.offsetAt(symbol.selectionRange.end),
    }));
}
function buildRichEditorTests(document) {
    return (0, testDiscovery_1.detectTestBlocks)(document).map((block) => ({
        kind: block.kind,
        label: block.label,
        line: block.line,
        from: document.offsetAt(new vscode.Position(block.line, 0)),
        to: document.offsetAt(new vscode.Position(block.line, document.lineAt(block.line).text.length)),
    }));
}
// ── Provider ─────────────────────────────────────────────────────────
class RichCustomEditorProvider {
    constructor(extensionUri, onActiveDocument) {
        this.extensionUri = extensionUri;
        this.onActiveDocument = onActiveDocument;
    }
    async resolveCustomTextEditor(document, webviewPanel, _token) {
        this.onActiveDocument?.(document);
        const katexDistUri = vscode.Uri.joinPath(this.extensionUri, 'node_modules', 'katex', 'dist');
        const webviewOutUri = vscode.Uri.joinPath(this.extensionUri, 'out', 'webview');
        const richEditorBundleUri = vscode.Uri.joinPath(webviewOutUri, 'richEditor.js');
        if (!fs.existsSync(richEditorBundleUri.fsPath)) {
            webviewPanel.webview.html = `<!DOCTYPE html>
<html lang="en">
<body style="font-family: sans-serif; padding: 24px;">
<h2>Simple Rich Editor bundle missing</h2>
<p>Expected webview bundle at:</p>
<pre>${richEditorBundleUri.fsPath}</pre>
<p>Run <code>npm run compile</code> in <code>src/app/vscode_extension</code> and reopen the editor.</p>
</body>
</html>`;
            return;
        }
        webviewPanel.webview.options = {
            enableScripts: true,
            localResourceRoots: [
                katexDistUri,
                webviewOutUri,
                ...(vscode.workspace.workspaceFolders?.map(wf => wf.uri) ?? []),
                vscode.Uri.joinPath(document.uri, '..'),
            ],
        };
        const katexCssUri = webviewPanel.webview.asWebviewUri(vscode.Uri.joinPath(katexDistUri, 'katex.min.css')).toString();
        const nonce = crypto.randomBytes(16).toString('base64url');
        const richEditorBundleSource = fs.readFileSync(richEditorBundleUri.fsPath, 'utf8')
            .replace(/<\/script>/gi, '<\\\\/script>');
        let selectionStart = 0;
        let selectionEnd = 0;
        let isApplyingEdit = false;
        const postSync = async () => {
            const text = document.getText();
            const detected = (0, blockDetector_1.detectBlocks)(text);
            const blocks = renderDetectedBlocks(detected, document.uri, webviewPanel.webview);
            await webviewPanel.webview.postMessage({
                type: 'sync',
                sourceText: text,
                selectionStart,
                selectionEnd,
                blocks,
                settings: getRichEditorSettings(),
                symbols: buildRichEditorSymbols(document),
                tests: buildRichEditorTests(document),
            });
        };
        webviewPanel.webview.html = buildRichEditorHtml(katexCssUri, richEditorBundleSource, webviewPanel.webview.cspSource, nonce);
        const changeDocumentSubscription = vscode.workspace.onDidChangeTextDocument(event => {
            if (event.document.uri.toString() !== document.uri.toString() || isApplyingEdit) {
                return;
            }
            void postSync();
        });
        const configurationSubscription = vscode.workspace.onDidChangeConfiguration((event) => {
            if (event.affectsConfiguration('simple.richEditor.showBlockBorders')
                || event.affectsConfiguration('simple.richEditor.centerLineNumbers')) {
                void postSync();
            }
        });
        const messageSubscription = webviewPanel.webview.onDidReceiveMessage(async (message) => {
            if (message.type === 'ready' || message.type === 'requestSync') {
                await postSync();
                return;
            }
            if (message.type === 'selectionChanged') {
                selectionStart = message.selectionStart;
                selectionEnd = message.selectionEnd;
                return;
            }
            if (message.type !== 'editAll') {
                return;
            }
            selectionStart = message.selectionStart;
            selectionEnd = message.selectionEnd;
            if (message.source === document.getText()) {
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
                        message: 'Failed to apply edit.',
                    });
                }
            }
            finally {
                isApplyingEdit = false;
            }
            return;
        });
        const runTestSubscription = webviewPanel.webview.onDidReceiveMessage(async (message) => {
            if (message.type !== 'runTestFromLine') {
                return;
            }
            const command = message.kind === 'sdoctest' ? 'simple.test.runSdoctest' : 'simple.test.runFile';
            await vscode.commands.executeCommand(command, document.uri);
        });
        webviewPanel.onDidDispose(() => {
            changeDocumentSubscription.dispose();
            configurationSubscription.dispose();
            messageSubscription.dispose();
            runTestSubscription.dispose();
        });
    }
}
exports.RichCustomEditorProvider = RichCustomEditorProvider;
RichCustomEditorProvider.viewType = 'simple.richSourceEditor';
//# sourceMappingURL=richCustomEditor.js.map