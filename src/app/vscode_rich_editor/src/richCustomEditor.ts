/**
 * Rich Custom Editor Provider for Simple language files.
 *
 * Provides a CodeMirror 6-based webview editor with:
 * - Variable line heights (math/images expand lines naturally)
 * - Cursor-aware view mode (non-cursor blocks render as widgets)
 * - Image embedding via img{} blocks
 * - Bi-directional sync with VSCode TextDocument
 */

import * as crypto from 'crypto';
import * as fs from 'fs';
import * as vscode from 'vscode';
import katex from 'katex';
import { detectBlocks, type BlockKind, type DetectedBlock } from './blockDetector';
import { parseImageContent, resolveImageUri } from './imageResolver';

// ── Types ────────────────────────────────────────────────────────────

export interface RenderableBlock {
    kind: BlockKind;
    from: number;
    to: number;
    content: string;
    prefix: string;
    renderedHtml: string;
    imageUri?: string;
    displayMode: 'inline' | 'block';
    status: 'ok' | 'error';
    errorMessage?: string;
}

type WebviewMessage =
    | { type: 'ready' }
    | { type: 'editAll'; source: string; selectionStart: number; selectionEnd: number }
    | { type: 'selectionChanged'; selectionStart: number; selectionEnd: number }
    | { type: 'requestSync' };

type HostMessage =
    | { type: 'sync'; sourceText: string; selectionStart: number; selectionEnd: number; blocks: RenderableBlock[] }
    | { type: 'error'; message: string };

// ── Math rendering (KaTeX) ───────────────────────────────────────────

const katexCache = new Map<string, string>();

function renderKatexInline(latex: string): string {
    const cached = katexCache.get(latex);
    if (cached !== undefined) return cached;
    let html: string;
    try {
        html = katex.renderToString(latex, {
            displayMode: true,
            throwOnError: false,
            output: 'html',
            trust: false,
        });
    } catch {
        html = '<span style="color: var(--vscode-errorForeground)">[math error]</span>';
    }
    katexCache.set(latex, html);
    return html;
}

/** Minimal Simple→LaTeX conversion for common patterns. */
function simpleToLatex(content: string): string {
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

function renderDetectedBlocks(
    blocks: DetectedBlock[],
    documentUri: vscode.Uri,
    webview: vscode.Webview,
): RenderableBlock[] {
    return blocks.map(block => {
        if (block.kind === 'img') {
            const parsed = parseImageContent(block.content);
            if (!parsed) {
                return {
                    ...block,
                    renderedHtml: '',
                    imageUri: undefined,
                    displayMode: 'block' as const,
                    status: 'error' as const,
                    errorMessage: 'Invalid image path',
                };
            }
            const uri = resolveImageUri(parsed.path, documentUri, webview);
            return {
                ...block,
                renderedHtml: '',
                imageUri: uri ?? undefined,
                displayMode: 'block' as const,
                status: uri ? 'ok' as const : 'error' as const,
                errorMessage: uri ? undefined : `Image not found: ${parsed.path}`,
            };
        }

        // Math/loss/nograd/graph — render via KaTeX
        const latex = simpleToLatex(block.content);
        const html = renderKatexInline(latex);
        return {
            ...block,
            renderedHtml: html,
            displayMode: 'inline' as const,
            status: 'ok' as const,
        };
    });
}

// ── HTML builder ─────────────────────────────────────────────────────

function buildRichEditorHtml(
    katexCssUri: string,
    richEditorJsUri: string,
    cspSource: string,
    nonce: string,
): string {
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
    <script nonce="${nonce}" src="${richEditorJsUri}"></script>
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
                    container.innerHTML =
                        '<div class="boot-error">' +
                        '<strong>Simple Rich Editor failed to start.</strong>' +
                        '<div>Check that the webview bundle exists and compiled successfully.</div>' +
                        '<div><code>' + message.replace(/</g, '&lt;') + '</code></div>' +
                        '</div>';
                }
            }
        })();
    </script>
</body>
</html>`;
}

// ── Helper ───────────────────────────────────────────────────────────

function fullDocumentRange(document: vscode.TextDocument): vscode.Range {
    const lastLine = document.lineCount > 0 ? document.lineAt(document.lineCount - 1) : undefined;
    const end = lastLine
        ? new vscode.Position(document.lineCount - 1, lastLine.text.length)
        : new vscode.Position(0, 0);
    return new vscode.Range(new vscode.Position(0, 0), end);
}

// ── Provider ─────────────────────────────────────────────────────────

export class RichCustomEditorProvider implements vscode.CustomTextEditorProvider {
    public static readonly viewType = 'simple.richSourceEditor';

    public constructor(private readonly extensionUri: vscode.Uri) {}

    public async resolveCustomTextEditor(
        document: vscode.TextDocument,
        webviewPanel: vscode.WebviewPanel,
        _token: vscode.CancellationToken,
    ): Promise<void> {
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
<p>Run <code>npm run compile</code> in <code>src/app/vscode_rich_editor</code> and reopen the editor.</p>
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

        const katexCssUri = webviewPanel.webview.asWebviewUri(
            vscode.Uri.joinPath(katexDistUri, 'katex.min.css'),
        ).toString();
        const richEditorJsUri = webviewPanel.webview.asWebviewUri(
            richEditorBundleUri,
        ).toString();
        const nonce = crypto.randomBytes(16).toString('base64url');

        let selectionStart = 0;
        let selectionEnd = 0;
        let isApplyingEdit = false;

        const postSync = async (): Promise<void> => {
            const text = document.getText();
            const detected = detectBlocks(text);
            const blocks = renderDetectedBlocks(detected, document.uri, webviewPanel.webview);
            await webviewPanel.webview.postMessage({
                type: 'sync',
                sourceText: text,
                selectionStart,
                selectionEnd,
                blocks,
            } satisfies HostMessage);
        };

        webviewPanel.webview.html = buildRichEditorHtml(
            katexCssUri,
            richEditorJsUri,
            webviewPanel.webview.cspSource,
            nonce,
        );

        const changeDocumentSubscription = vscode.workspace.onDidChangeTextDocument(event => {
            if (event.document.uri.toString() !== document.uri.toString() || isApplyingEdit) {
                return;
            }
            void postSync();
        });

        const messageSubscription = webviewPanel.webview.onDidReceiveMessage(async (message: WebviewMessage) => {
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
                    } satisfies HostMessage);
                }
            } finally {
                isApplyingEdit = false;
            }
        });

        webviewPanel.onDidDispose(() => {
            changeDocumentSubscription.dispose();
            messageSubscription.dispose();
        });
    }
}
