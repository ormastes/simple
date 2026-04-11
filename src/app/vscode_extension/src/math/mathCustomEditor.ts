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
    content: string;
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
    | { type: 'sync'; state: MathCustomEditorState }
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

function emptyState(
    documentUri: string,
    sourceText: string,
    selectionStart: number,
    selectionEnd: number,
): MathCustomEditorState {
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
        return emptyState(documentUri, sourceText, clippedSelectionStart, clippedSelectionEnd);
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

function statusClassName(kind: MathRenderStatusKind): string {
    switch (kind) {
        case 'error':
            return 'status status-error';
        case 'ok':
            return 'status status-ok';
        default:
            return 'status status-info';
    }
}

function escapeAttribute(value: string): string {
    return escapeForHtml(value);
}

function renderStatusMessage(state: MathCustomEditorState): string {
    return escapeForHtml(state.activeBlockStatusMessage);
}

function renderStatusClass(state: MathCustomEditorState): string {
    return escapeAttribute(statusClassName(state.activeBlockStatusKind));
}

function renderStatusKind(kind: MathRenderStatusKind): string {
    return kind;
}

function dataStatusKind(state: MathCustomEditorState): string {
    return escapeAttribute(renderStatusKind(state.activeBlockStatusKind));
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

export function detectMathBlocksInSource(text: string): MathBlockSnapshot[] {
    const blocks: MathBlockSnapshot[] = [];
    MATH_BLOCK_REGEX.lastIndex = 0;

    let match: RegExpExecArray | null;
    while ((match = MATH_BLOCK_REGEX.exec(text)) !== null) {
        const prefix = match.groups?.prefix ?? 'm';
        const blockType: MathBlockType =
            prefix === 'loss' ? 'loss' :
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

export function findMathBlockAtOffset(text: string, offset: number): MathBlockSnapshot | undefined {
    const clippedOffset = Math.max(0, Math.min(text.length, offset));
    return detectMathBlocksInSource(text).find(block =>
        clippedOffset >= block.fullStart && clippedOffset <= block.fullEnd,
    );
}

export function buildMathCustomEditorHtml(
    state: MathCustomEditorState,
    katexCssUri?: string,
    cspSource?: string,
): string {
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
        const katexCssUri = webviewPanel.webview.asWebviewUri(
            vscode.Uri.joinPath(katexDistUri, 'katex.min.css'),
        ).toString();
        webviewPanel.webview.options = {
            enableScripts: true,
            localResourceRoots: [katexDistUri],
        };

        let selectionStart = 0;
        let selectionEnd = 0;
        let isApplyingEdit = false;

        const postState = async (): Promise<void> => {
            await webviewPanel.webview.postMessage({
                type: 'sync',
                state: makeState(document, selectionStart, selectionEnd),
            } satisfies MathCustomEditorHostMessage);
        };

        webviewPanel.webview.html = buildMathCustomEditorHtml(
            makeState(document, selectionStart, selectionEnd),
            katexCssUri,
            webviewPanel.webview.cspSource,
        );

        const changeDocumentSubscription = vscode.workspace.onDidChangeTextDocument(event => {
            if (event.document.uri.toString() !== document.uri.toString() || isApplyingEdit) {
                return;
            }
            void postState();
        });

        const messageSubscription = webviewPanel.webview.onDidReceiveMessage(async (message: MathCustomEditorMessage) => {
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
                    } satisfies MathCustomEditorHostMessage);
                }
            } finally {
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
