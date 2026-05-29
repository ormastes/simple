/**
 * Math Sync Panel - webview companion that mirrors the active math block and
 * delegates edits back to the source document.
 *
 * The source editor remains canonical. This panel is a synchronized view with a
 * local source textarea, rendered preview, and edit delegation through normal
 * VS Code document edits so undo/redo and diagnostics stay owned by the editor.
 */

import * as crypto from 'crypto';
import * as vscode from 'vscode';
import katex from 'katex';
import { MathBlockRange, MathDecorationProvider } from './mathDecorationProvider';
import { simpleToLatex, simpleToUnicode } from './mathConverter';

export interface MathSyncPanelState {
    documentUri: string;
    blockText: string;
    latex: string;
    pretty: string;
    renderedHtml: string;
    blockLabel: string;
    selectionStart: number;
    selectionEnd: number;
    hasContent: boolean;
}

type MathSyncPanelMessage =
    | { type: 'ready' }
    | { type: 'edit'; source: string }
    | { type: 'request-sync' };

type MathSyncPanelHostMessage =
    | { type: 'sync'; state: MathSyncPanelState }
    | { type: 'empty'; message: string }
    | { type: 'error'; message: string };

function escapeForHtml(text: string): string {
    return text
        .replace(/&/g, '&amp;')
        .replace(/</g, '&lt;')
        .replace(/>/g, '&gt;')
        .replace(/"/g, '&quot;')
        .replace(/'/g, '&#039;');
}

function buildHighlightedSourcePreview(text: string, selectionStart: number, selectionEnd: number): string {
    const start = Math.max(0, Math.min(text.length, selectionStart));
    const end = Math.max(start, Math.min(text.length, selectionEnd));
    const before = escapeForHtml(text.slice(0, start));
    const selected = escapeForHtml(text.slice(start, end));
    const after = escapeForHtml(text.slice(end));
    const selectedHtml = selected.length > 0
        ? `<span class="selection-highlight">${selected}</span>`
        : '<span class="selection-caret">|</span>';
    return `${before}${selectedHtml}${after}`;
}

function renderKatex(latex: string): string {
    try {
        return katex.renderToString(latex, {
            displayMode: true,
            throwOnError: false,
            output: 'html',
            trust: false,
        });
    } catch {
        return `<span class="katex-error">${escapeForHtml(latex)}</span>`;
    }
}

function formatBlockLabel(blockType: MathBlockRange['blockType']): string {
    switch (blockType) {
        case 'loss':
            return 'loss{}';
        case 'nograd':
            return 'nograd{}';
        default:
            return 'm{}';
    }
}

export function findMathBlockAtPosition(
    provider: MathDecorationProvider,
    document: vscode.TextDocument,
    position: vscode.Position,
): MathBlockRange | undefined {
    return provider.detectMathBlocks(document).find(block => block.fullRange.contains(position));
}

function offsetAtText(text: string, position: vscode.Position): number {
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

export function replaceRangeInText(text: string, range: vscode.Range, replacement: string): string {
    const start = Math.max(0, Math.min(text.length, offsetAtText(text, range.start)));
    const end = Math.max(start, Math.min(text.length, offsetAtText(text, range.end)));
    return `${text.slice(0, start)}${replacement}${text.slice(end)}`;
}

export function buildMathSyncPanelHtml(
    state: MathSyncPanelState,
    katexCssUri?: string,
    cspSource?: string,
): string {
    const nonce = crypto.randomBytes(16).toString('base64');
    const sourceValue = escapeForHtml(state.blockText);
    const prettyValue = escapeForHtml(state.pretty);
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
        .panel-state.active .section {
            border-color: var(--vscode-focusBorder);
            box-shadow: 0 0 0 1px var(--vscode-focusBorder) inset;
        }
        .panel-state.sync-pending .section {
            border-color: var(--vscode-progressBar-background);
            box-shadow: 0 0 0 1px var(--vscode-progressBar-background) inset;
        }
        .panel-state.active .section-label {
            color: var(--vscode-focusBorder);
        }
        .panel-state.sync-pending .section-label {
            color: var(--vscode-progressBar-background);
        }
        .active-strip {
            display: none;
            margin-bottom: 12px;
            padding: 8px 10px;
            border-radius: 4px;
            background: color-mix(in srgb, var(--vscode-focusBorder) 16%, transparent);
            border: 1px solid var(--vscode-focusBorder);
            color: var(--vscode-foreground);
            font-size: 11px;
        }
        .panel-state.active .active-strip {
            display: block;
        }
        .panel-state.sync-pending .active-strip {
            display: block;
            border-style: dashed;
            background: color-mix(in srgb, var(--vscode-progressBar-background) 18%, transparent);
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
        .selection-highlight {
            background: color-mix(in srgb, var(--vscode-focusBorder) 28%, transparent);
            color: var(--vscode-foreground);
            border-radius: 3px;
            padding: 0 2px;
            border: 1px solid var(--vscode-focusBorder);
        }
        .selection-caret {
            color: var(--vscode-focusBorder);
            font-weight: 700;
        }
    </style>
</head>
<body>
    <div id="panel-root" class="panel-state${state.hasContent ? ' active' : ''}">
        <h2>Math Sync Panel</h2>
        <div class="meta">
            <div>Document: <span id="doc-uri">${escapeForHtml(state.documentUri)}</span></div>
            <div>Selection: <span id="selection">${state.selectionStart}-${state.selectionEnd}</span></div>
            <div>Block: <span id="block-label">${escapeForHtml(state.blockLabel)}</span></div>
        </div>

        <div class="grid">
            <div class="active-strip" id="active-strip">Active math block is mirrored from the source editor</div>

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
                <div class="source-preview" id="source-preview">${state.hasContent ? `Source mirror: ${buildHighlightedSourcePreview(state.blockText, state.selectionStart, state.selectionEnd)}` : ''}</div>
            </div>
        </div>
    </div>

    <script nonce="${nonce}">
        const vscode = acquireVsCodeApi();
        const root = document.getElementById('panel-root');
        const activeStrip = document.getElementById('active-strip');
        const source = document.getElementById('math-source');
        const rendered = document.getElementById('math-rendered');
        const pretty = document.getElementById('pretty');
        const selection = document.getElementById('selection');
        const blockLabel = document.getElementById('block-label');
        const docUri = document.getElementById('doc-uri');
        const sourcePreview = document.getElementById('source-preview');
        const refreshButton = document.getElementById('refresh-button');

        let timer = null;
        let syncPending = false;

        function setPending(pending) {
            syncPending = pending;
            root.classList.toggle('sync-pending', pending);
            if (pending) {
                activeStrip.textContent = 'Syncing math block changes...';
            } else {
                activeStrip.textContent = 'Active math block is mirrored from the source editor';
            }
        }

        function escapeHtml(text) {
            return text
                .replace(/&/g, '&amp;')
                .replace(/</g, '&lt;')
                .replace(/>/g, '&gt;')
                .replace(/"/g, '&quot;')
                .replace(/'/g, '&#039;');
        }

        function renderSourcePreview(text, start, end) {
            const clippedStart = Math.max(0, Math.min(text.length, start));
            const clippedEnd = Math.max(clippedStart, Math.min(text.length, end));
            const before = escapeHtml(text.slice(0, clippedStart));
            const selected = escapeHtml(text.slice(clippedStart, clippedEnd));
            const after = escapeHtml(text.slice(clippedEnd));
            const selectedHtml = selected.length > 0
                ? '<span class="selection-highlight">' + selected + '</span>'
                : '<span class="selection-caret">|</span>';
            return 'Source mirror: ' + before + selectedHtml + after;
        }

        function sendEdit() {
            setPending(true);
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
                setPending(false);
                root.classList.toggle('active', state.hasContent);
                activeStrip.style.display = state.hasContent ? 'block' : 'none';
                docUri.textContent = state.documentUri;
                selection.textContent = state.selectionStart + '-' + state.selectionEnd;
                blockLabel.textContent = state.blockLabel;
                pretty.textContent = state.hasContent ? 'Pretty: ' + state.pretty : '';
                sourcePreview.innerHTML = state.hasContent
                    ? renderSourcePreview(state.blockText, state.selectionStart, state.selectionEnd)
                    : '';
                if (source.value !== state.blockText) {
                    source.value = state.blockText;
                }
                if (typeof source.setSelectionRange === 'function') {
                    source.setSelectionRange(state.selectionStart, state.selectionEnd);
                }
                if (state.hasContent) {
                    rendered.innerHTML = state.renderedHtml;
                } else {
                    rendered.innerHTML = '<div class="empty-state">Move the cursor onto a math block in the source editor.</div>';
                }
            } else if (msg.type === 'empty') {
                setPending(false);
                rendered.innerHTML = '<div class="empty-state">' + msg.message + '</div>';
                pretty.textContent = '';
                sourcePreview.innerHTML = '';
                source.value = '';
            } else if (msg.type === 'error') {
                setPending(false);
                rendered.innerHTML = '<div class="empty-state">' + msg.message + '</div>';
            }
        });

        vscode.postMessage({ type: 'ready' });
    </script>
</body>
</html>`;
}

function makeState(
    document: vscode.TextDocument,
    uri: vscode.Uri,
    block: MathBlockRange,
    selection: vscode.Selection,
): MathSyncPanelState {
    const latex = simpleToLatex(block.content);
    const pretty = simpleToUnicode(block.content);
    const renderedHtml = renderKatex(latex);
    const selectionStart = Math.max(
        0,
        document.offsetAt(selection.start) - document.offsetAt(block.contentRange.start)
    );
    const selectionEnd = Math.max(
        selectionStart,
        document.offsetAt(selection.end) - document.offsetAt(block.contentRange.start)
    );
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

export class MathSyncPanel implements vscode.Disposable {
    public static currentPanel: MathSyncPanel | undefined;

    private readonly panel: vscode.WebviewPanel;
    private readonly decorationProvider: MathDecorationProvider;
    private readonly extensionUri: vscode.Uri;
    private readonly katexCssUri: string;
    private disposables: vscode.Disposable[] = [];
    private currentDocumentUri: vscode.Uri | undefined;
    private lastStateKey: string | undefined;
    private syncTimer: ReturnType<typeof setTimeout> | undefined;

    private constructor(
        panel: vscode.WebviewPanel,
        decorationProvider: MathDecorationProvider,
        extensionUri: vscode.Uri
    ) {
        this.panel = panel;
        this.decorationProvider = decorationProvider;
        this.extensionUri = extensionUri;
        this.katexCssUri = this.panel.webview.asWebviewUri(
            vscode.Uri.joinPath(extensionUri, 'node_modules', 'katex', 'dist', 'katex.min.css')
        ).toString();

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
        }, this.katexCssUri, this.panel.webview.cspSource);

        this.disposables.push(
            this.panel.webview.onDidReceiveMessage((message: MathSyncPanelMessage) => {
                void this.handleMessage(message);
            })
        );
        this.disposables.push(
            vscode.window.onDidChangeTextEditorSelection((event) => this.handleSelectionChange(event))
        );
        this.disposables.push(
            vscode.workspace.onDidChangeTextDocument((event) => this.handleDocumentChange(event))
        );
        this.panel.onDidDispose(() => this.dispose(), null, this.disposables);

        const editor = vscode.window.activeTextEditor;
        if (editor) {
            this.syncFromEditor(editor);
        }
    }

    public static show(decorationProvider: MathDecorationProvider, extensionUri: vscode.Uri): void {
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
        const panel = vscode.window.createWebviewPanel(
            'simpleMathSyncPanel',
            'Math Sync Panel',
            {
                viewColumn: vscode.ViewColumn.Beside,
                preserveFocus: true,
            },
            {
                enableScripts: true,
                retainContextWhenHidden: true,
                localResourceRoots: [katexDistUri],
            }
        );

        MathSyncPanel.currentPanel = new MathSyncPanel(panel, decorationProvider, extensionUri);
    }

    public static isVisible(): boolean {
        return MathSyncPanel.currentPanel !== undefined;
    }

    public static close(): void {
        if (MathSyncPanel.currentPanel) {
            MathSyncPanel.currentPanel.panel.dispose();
        }
    }

    private async handleMessage(message: MathSyncPanelMessage): Promise<void> {
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

    private handleSelectionChange(event: vscode.TextEditorSelectionChangeEvent): void {
        if (!this.currentDocumentUri || event.textEditor.document.uri.toString() !== this.currentDocumentUri.toString()) {
            return;
        }
        this.scheduleSyncFromEditor(event.textEditor);
    }

    private handleDocumentChange(event: vscode.TextDocumentChangeEvent): void {
        if (!this.currentDocumentUri || event.document.uri.toString() !== this.currentDocumentUri.toString()) {
            return;
        }
        const editor = this.getEditorForCurrentDocument();
        if (editor) {
            this.scheduleSyncFromEditor(editor);
        }
    }

    private scheduleSyncFromEditor(editor: vscode.TextEditor): void {
        if (this.syncTimer) {
            clearTimeout(this.syncTimer);
        }
        this.syncTimer = setTimeout(() => {
            this.syncTimer = undefined;
            this.syncFromEditor(editor);
        }, 50);
    }

    private getEditorForCurrentDocument(): vscode.TextEditor | undefined {
        if (!this.currentDocumentUri) {
            return vscode.window.activeTextEditor;
        }
        return vscode.window.visibleTextEditors.find(editor =>
            editor.document.uri.toString() === this.currentDocumentUri?.toString()
        ) ?? vscode.window.activeTextEditor;
    }

    private getCurrentBlock(document: vscode.TextDocument): MathBlockRange | undefined {
        const editor = vscode.window.visibleTextEditors.find(e => e.document.uri.toString() === document.uri.toString());
        const position = editor?.selection.active ?? new vscode.Position(0, 0);
        return findMathBlockAtPosition(this.decorationProvider, document, position);
    }

    private syncFromEditor(editor: vscode.TextEditor): void {
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
            } satisfies MathSyncPanelHostMessage);
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
        } satisfies MathSyncPanelHostMessage);
    }

    public dispose(): void {
        MathSyncPanel.currentPanel = undefined;
        if (this.syncTimer) {
            clearTimeout(this.syncTimer);
            this.syncTimer = undefined;
        }
        this.panel.dispose();
        for (const disposable of this.disposables) {
            disposable.dispose();
        }
        this.disposables = [];
    }
}
