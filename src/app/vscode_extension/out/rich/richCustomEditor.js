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
const vscode = __importStar(require("vscode"));
const katex_1 = __importDefault(require("katex"));
const blockDetector_1 = require("./blockDetector");
const imageResolver_1 = require("./imageResolver");
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
/** Minimal Simple→LaTeX conversion for common patterns. */
function simpleToLatex(content) {
    let s = content;
    // Greek letters
    const greeks = [
        'alpha', 'beta', 'gamma', 'delta', 'epsilon', 'zeta', 'eta', 'theta',
        'iota', 'kappa', 'lambda', 'mu', 'nu', 'xi', 'pi', 'rho', 'sigma',
        'tau', 'upsilon', 'phi', 'chi', 'psi', 'omega',
        'Gamma', 'Delta', 'Theta', 'Lambda', 'Xi', 'Pi', 'Sigma', 'Phi', 'Psi', 'Omega',
    ];
    for (const g of greeks) {
        s = s.replace(new RegExp(`\\b${g}\\b`, 'g'), `\\${g}`);
    }
    // Functions
    s = s.replace(/\bfrac\(([^,]+),\s*([^)]+)\)/g, '\\frac{$1}{$2}');
    s = s.replace(/\bsqrt\(([^)]+)\)/g, '\\sqrt{$1}');
    s = s.replace(/\bsum\b/g, '\\sum');
    s = s.replace(/\bprod\b/g, '\\prod');
    s = s.replace(/\bint\b/g, '\\int');
    s = s.replace(/\blim\b/g, '\\lim');
    s = s.replace(/\binf\b/g, '\\infty');
    // Trig/log
    for (const fn of ['sin', 'cos', 'tan', 'log', 'ln', 'exp', 'det', 'max', 'min']) {
        s = s.replace(new RegExp(`\\b${fn}\\b`, 'g'), `\\${fn}`);
    }
    return s;
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
        const latex = simpleToLatex(block.content);
        const html = renderKatexInline(latex);
        return {
            ...block,
            renderedHtml: html,
            displayMode: 'inline',
            status: 'ok',
        };
    });
}
// ── HTML builder ─────────────────────────────────────────────────────
function buildRichEditorHtml(katexCssUri, richEditorJsUri, cspSource, nonce) {
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
                   script-src 'nonce-${nonce}';">
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
        }
    </style>
</head>
<body>
    <div id="editor-container"></div>
    <script nonce="${nonce}" src="${richEditorJsUri}"></script>
    <script nonce="${nonce}">
        RichEditorWebview.boot();
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
// ── Provider ─────────────────────────────────────────────────────────
class RichCustomEditorProvider {
    constructor(extensionUri) {
        this.extensionUri = extensionUri;
    }
    async resolveCustomTextEditor(document, webviewPanel, _token) {
        const katexDistUri = vscode.Uri.joinPath(this.extensionUri, 'node_modules', 'katex', 'dist');
        const webviewOutUri = vscode.Uri.joinPath(this.extensionUri, 'out', 'webview');
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
        const richEditorJsUri = webviewPanel.webview.asWebviewUri(vscode.Uri.joinPath(webviewOutUri, 'richEditor.js')).toString();
        const nonce = crypto.randomBytes(16).toString('base64url');
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
            });
        };
        webviewPanel.webview.html = buildRichEditorHtml(katexCssUri, richEditorJsUri, webviewPanel.webview.cspSource, nonce);
        const changeDocumentSubscription = vscode.workspace.onDidChangeTextDocument(event => {
            if (event.document.uri.toString() !== document.uri.toString() || isApplyingEdit) {
                return;
            }
            void postSync();
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
            // editAll
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
        });
        webviewPanel.onDidDispose(() => {
            changeDocumentSubscription.dispose();
            messageSubscription.dispose();
        });
    }
}
exports.RichCustomEditorProvider = RichCustomEditorProvider;
RichCustomEditorProvider.viewType = 'simple.richSourceEditor';
//# sourceMappingURL=richCustomEditor.js.map