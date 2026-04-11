import * as crypto from 'crypto';
import * as vscode from 'vscode';
import katex from 'katex';
import { simpleToLatex, simpleToUnicode } from './mathConverter';

type MathBlockType = 'math' | 'loss' | 'nograd';

const MATH_BLOCK_REGEX = /\b(?<prefix>m|loss|nograd)\{([^}]*(?:\{[^}]*\}[^}]*)*)\}/gs;

interface MathBlockSnapshot {
    blockType: MathBlockType;
    fullStart: number;
    fullEnd: number;
    prefixEnd: number;
    content: string;
    prefix: string;
    renderedHtml: string;
}

type MathRenderStatusKind = 'info' | 'ok' | 'error';

export interface MathCustomEditorState {
    documentUri: string;
    sourceText: string;
    selectionStart: number;
    selectionEnd: number;
    hasActiveBlock: boolean;
    activeBlockLabel: string;
    activeBlockSource: string;
    activeBlockPretty: string;
    activeBlockRenderedHtml: string;
    activeBlockStatusKind: MathRenderStatusKind;
    activeBlockStatusMessage: string;
}

type MathCustomEditorMessage =
    | { type: 'ready' }
    | { type: 'editAll'; source: string; selectionStart: number; selectionEnd: number }
    | { type: 'selectionChanged'; selectionStart: number; selectionEnd: number }
    | { type: 'requestSync' };

type MathCustomEditorHostMessage =
    | { type: 'sync'; sourceText: string; selectionStart: number; selectionEnd: number; mathBlocks: MathBlockSnapshot[] }
    | { type: 'focusedBlock'; html: string; label: string; source: string; pretty: string; statusKind: string; statusMessage: string; hasContent: boolean }
    | { type: 'error'; message: string };

interface KatexRenderResult {
    html: string;
    statusKind: MathRenderStatusKind;
    statusMessage: string;
}

function escapeForHtml(text: string): string {
    return text
        .replace(/&/g, '&amp;')
        .replace(/</g, '&lt;')
        .replace(/>/g, '&gt;')
        .replace(/"/g, '&quot;')
        .replace(/'/g, '&#039;');
}

function renderKatex(latex: string): KatexRenderResult {
    try {
        return {
            html: katex.renderToString(latex, {
                displayMode: true,
                throwOnError: true,
                output: 'html',
                trust: false,
            }),
            statusKind: 'ok',
            statusMessage: 'Rendered active math block.',
        };
    } catch (error) {
        return {
            html: `<div class="render-fallback"><div class="katex-error">Could not render the active math block.</div><div class="preview-text">${escapeForHtml(latex)}</div></div>`,
            statusKind: 'error',
            statusMessage: error instanceof Error ? error.message : 'Could not render the active math block.',
        };
    }
}

const katexInlineCache = new Map<string, string>();

/** Render KaTeX for inline widget display (not clamped — natural height). Cached by latex string. */
function renderKatexInline(latex: string): string {
    const cached = katexInlineCache.get(latex);
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
        html = `<span style="color: var(--vscode-errorForeground)">[math error]</span>`;
    }
    katexInlineCache.set(latex, html);
    return html;
}

export function detectMathBlocksInSource(text: string): MathBlockSnapshot[] {
    const blocks: MathBlockSnapshot[] = [];
    MATH_BLOCK_REGEX.lastIndex = 0;

    let match: RegExpExecArray | null;
    while ((match = MATH_BLOCK_REGEX.exec(text)) !== null) {
        const prefix = match.groups?.prefix ?? 'm';
        const blockType: MathBlockType =
            prefix === 'loss' ? 'loss' :
            prefix === 'nograd' ? 'nograd' : 'math';

        const content = match[2].trim();
        const latex = simpleToLatex(content);
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

export function findMathBlockAtOffset(text: string, offset: number): MathBlockSnapshot | undefined {
    const clippedOffset = Math.max(0, Math.min(text.length, offset));
    return detectMathBlocksInSource(text).find(block =>
        clippedOffset >= block.fullStart && clippedOffset <= block.fullEnd,
    );
}

function formatBlockLabel(blockType: MathBlockType): string {
    switch (blockType) {
        case 'loss':
            return 'loss{}';
        case 'nograd':
            return 'nograd{}';
        default:
            return 'm{}';
    }
}

export function buildMathCustomEditorState(
    documentUri: string,
    sourceText: string,
    selectionStart: number,
    selectionEnd: number,
): MathCustomEditorState {
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

    const latex = simpleToLatex(block.content);
    const renderResult = renderKatex(latex);
    return {
        documentUri,
        sourceText,
        selectionStart: clippedSelectionStart,
        selectionEnd: clippedSelectionEnd,
        hasActiveBlock: true,
        activeBlockLabel: formatBlockLabel(block.blockType),
        activeBlockSource: block.content,
        activeBlockPretty: simpleToUnicode(block.content),
        activeBlockRenderedHtml: renderResult.html,
        activeBlockStatusKind: renderResult.statusKind,
        activeBlockStatusMessage: renderResult.statusMessage,
    };
}

function makeState(document: vscode.TextDocument, selectionStart: number, selectionEnd: number): MathCustomEditorState {
    return buildMathCustomEditorState(
        document.uri.toString(),
        document.getText(),
        selectionStart,
        selectionEnd,
    );
}

// ── HTML builder ─────────────────────────────────────────────────────

export function buildMathCustomEditorHtml(
    katexCssUri: string,
    webviewJsUri: string,
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

function fullDocumentRange(document: vscode.TextDocument): vscode.Range {
    const lastLine = document.lineCount > 0 ? document.lineAt(document.lineCount - 1) : undefined;
    const end = lastLine
        ? new vscode.Position(document.lineCount - 1, lastLine.text.length)
        : new vscode.Position(0, 0);
    return new vscode.Range(new vscode.Position(0, 0), end);
}

export class MathCustomEditorProvider implements vscode.CustomTextEditorProvider {
    public static readonly viewType = 'simple.mathSourceEditor';

    public constructor(private readonly extensionUri: vscode.Uri) {}

    public async resolveCustomTextEditor(
        document: vscode.TextDocument,
        webviewPanel: vscode.WebviewPanel,
        _token: vscode.CancellationToken,
    ): Promise<void> {
        const katexDistUri = vscode.Uri.joinPath(this.extensionUri, 'node_modules', 'katex', 'dist');
        const webviewOutUri = vscode.Uri.joinPath(this.extensionUri, 'out', 'webview');

        webviewPanel.webview.options = {
            enableScripts: true,
            localResourceRoots: [katexDistUri, webviewOutUri],
        };

        const katexCssUri = webviewPanel.webview.asWebviewUri(
            vscode.Uri.joinPath(katexDistUri, 'katex.min.css'),
        ).toString();
        const webviewJsUri = webviewPanel.webview.asWebviewUri(
            vscode.Uri.joinPath(webviewOutUri, 'mathEditor.js'),
        ).toString();
        const nonce = crypto.randomBytes(16).toString('base64');

        console.log('[math-editor] katexCssUri:', katexCssUri);
        console.log('[math-editor] webviewJsUri:', webviewJsUri);
        console.log('[math-editor] cspSource:', webviewPanel.webview.cspSource);
        console.log('[math-editor] localResourceRoots:', [katexDistUri.fsPath, webviewOutUri.fsPath]);

        let selectionStart = 0;
        let selectionEnd = 0;
        let isApplyingEdit = false;

        const postSync = async (): Promise<void> => {
            const text = document.getText();
            const mathBlocks = detectMathBlocksInSource(text);
            await webviewPanel.webview.postMessage({
                type: 'sync',
                sourceText: text,
                selectionStart,
                selectionEnd,
                mathBlocks,
            } satisfies MathCustomEditorHostMessage);
        };

        const postFocusedBlock = async (): Promise<void> => {
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
            } satisfies MathCustomEditorHostMessage);
        };

        // Set initial HTML
        webviewPanel.webview.html = buildMathCustomEditorHtml(
            katexCssUri,
            webviewJsUri,
            webviewPanel.webview.cspSource,
            nonce,
        );

        const changeDocumentSubscription = vscode.workspace.onDidChangeTextDocument(event => {
            if (event.document.uri.toString() !== document.uri.toString() || isApplyingEdit) {
                return;
            }
            void postSync();
        });

        const messageSubscription = webviewPanel.webview.onDidReceiveMessage(async (message: MathCustomEditorMessage) => {
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
                    } satisfies MathCustomEditorHostMessage);
                }
            } finally {
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
