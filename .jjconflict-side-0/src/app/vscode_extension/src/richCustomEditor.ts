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
import { analyzeDocument } from './analysis/simpleAnalysisIndex';
import { detectBlocks } from './blockDetector';
import { createWebviewImageResolver, renderRichBlocks, type RenderableBlock } from './richBlockRendering';
import type { EditorMarkerState } from './testing/editorMarkers';

interface RichEditorSettings {
    showBlockBorders: boolean;
    centerLineNumbers: boolean;
}

interface RichEditorSymbol {
    name: string;
    kind: string;
    detail: string;
    line: number;
    from: number;
    to: number;
}

interface RichEditorTestBlock {
    id: string;
    kind: string;
    label: string;
    line: number;
    from: number;
    to: number;
    runnableScope: 'file' | 'doctest' | 'exact' | 'none';
    status: 'idle' | 'running' | 'passed' | 'failed' | 'skipped';
}

interface RichEditorMarkers {
    breakpoints: number[];
    bookmarks: number[];
    pointerLine: number | null;
}

type WebviewMessage =
    | { type: 'ready' }
    | { type: 'editAll'; source: string; selectionStart: number; selectionEnd: number }
    | { type: 'selectionChanged'; selectionStart: number; selectionEnd: number }
    | { type: 'requestSync' }
    | { type: 'runTestFromLine'; line: number; kind: string; label: string }
    | { type: 'toggleBreakpointFromLine'; line: number }
    | { type: 'toggleBookmarkFromLine'; line: number }
    | { type: 'togglePointerFromLine'; line: number }
    | { type: 'revealDefinition'; offset: number }
    | { type: 'showReferences'; offset: number };

type HostMessage =
    | {
        type: 'sync';
        sourceText: string;
        selectionStart: number;
        selectionEnd: number;
        blocks: RenderableBlock[];
        settings: RichEditorSettings;
        symbols: RichEditorSymbol[];
        tests: RichEditorTestBlock[];
        markers: RichEditorMarkers;
    }
    | { type: 'error'; message: string };

function getRichEditorSettings(): RichEditorSettings {
    const config = vscode.workspace.getConfiguration('simple.richEditor');
    return {
        showBlockBorders: config.get<boolean>('showBlockBorders', false),
        centerLineNumbers: config.get<boolean>('centerLineNumbers', true),
    };
}

// ── HTML builder ─────────────────────────────────────────────────────

function buildRichEditorHtml(
    katexCssUri: string,
    richEditorBundleSource: string,
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

function fullDocumentRange(document: vscode.TextDocument): vscode.Range {
    const lastLine = document.lineCount > 0 ? document.lineAt(document.lineCount - 1) : undefined;
    const end = lastLine
        ? new vscode.Position(document.lineCount - 1, lastLine.text.length)
        : new vscode.Position(0, 0);
    return new vscode.Range(new vscode.Position(0, 0), end);
}

function buildRichEditorSymbols(document: vscode.TextDocument): RichEditorSymbol[] {
    return analyzeDocument(document).symbols.map((symbol) => ({
        name: symbol.name,
        kind: vscode.SymbolKind[symbol.kind],
        detail: symbol.detail,
        line: symbol.selectionRange.start.line,
        from: document.offsetAt(symbol.selectionRange.start),
        to: document.offsetAt(symbol.selectionRange.end),
    }));
}

function buildRichEditorTests(document: vscode.TextDocument): RichEditorTestBlock[] {
    return analyzeDocument(document).tests.map((block) => ({
        id: block.id,
        kind: block.kind,
        label: block.label,
        line: block.line,
        from: document.offsetAt(new vscode.Position(block.line, 0)),
        to: document.offsetAt(new vscode.Position(block.line, document.lineAt(block.line).text.length)),
        runnableScope: block.runnableScope,
        status: 'idle',
    }));
}

// ── Provider ─────────────────────────────────────────────────────────

export class RichCustomEditorProvider implements vscode.CustomTextEditorProvider {
    public static readonly viewType = 'simple.richSourceEditor';

    public constructor(
        private readonly extensionUri: vscode.Uri,
        private readonly onActiveDocument?: (document: vscode.TextDocument) => void,
        private readonly getMarkerState?: (documentUri: vscode.Uri) => EditorMarkerState,
        private readonly onDidChangeMarkers?: vscode.Event<vscode.Uri>,
        private readonly getTestStates?: (documentUri: vscode.Uri) => ReadonlyMap<string, 'idle' | 'running' | 'passed' | 'failed' | 'skipped'>,
        private readonly onDidChangeTestStates?: vscode.Event<vscode.Uri>,
    ) {}

    public async resolveCustomTextEditor(
        document: vscode.TextDocument,
        webviewPanel: vscode.WebviewPanel,
        _token: vscode.CancellationToken,
    ): Promise<void> {
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

        const katexCssUri = webviewPanel.webview.asWebviewUri(
            vscode.Uri.joinPath(katexDistUri, 'katex.min.css'),
        ).toString();
        const nonce = crypto.randomBytes(16).toString('base64url');
        const richEditorBundleSource = fs.readFileSync(richEditorBundleUri.fsPath, 'utf8')
            .replace(/<\/script>/gi, '<\\\\/script>');

        let selectionStart = 0;
        let selectionEnd = 0;
        let isApplyingEdit = false;

        const postSync = async (): Promise<void> => {
            const text = document.getText();
            const detected = detectBlocks(text);
            const blocks = renderRichBlocks({
                blocks: detected,
                document,
                resolveImageUri: createWebviewImageResolver(webviewPanel.webview),
            });
            const testStates = this.getTestStates?.(document.uri);
            await webviewPanel.webview.postMessage({
                type: 'sync',
                sourceText: text,
                selectionStart,
                selectionEnd,
                blocks,
                settings: getRichEditorSettings(),
                symbols: buildRichEditorSymbols(document),
                tests: buildRichEditorTests(document).map((test) => ({
                    ...test,
                    status: testStates?.get(test.id) ?? 'idle',
                })),
                markers: this.getMarkerState
                    ? this.getMarkerState(document.uri)
                    : { breakpoints: [], bookmarks: [], pointerLine: null },
            } satisfies HostMessage);
        };

        webviewPanel.webview.html = buildRichEditorHtml(
            katexCssUri,
            richEditorBundleSource,
            webviewPanel.webview.cspSource,
            nonce,
        );

        const changeDocumentSubscription = vscode.workspace.onDidChangeTextDocument(event => {
            if (event.document.uri.toString() !== document.uri.toString() || isApplyingEdit) {
                return;
            }
            void postSync();
        });

        const configurationSubscription = vscode.workspace.onDidChangeConfiguration((event) => {
            if (
                event.affectsConfiguration('simple.richEditor.showBlockBorders')
                || event.affectsConfiguration('simple.richEditor.centerLineNumbers')
            ) {
                void postSync();
            }
        });
        const markerChangeSubscription = this.onDidChangeMarkers?.((changedUri) => {
            if (changedUri.toString() === document.uri.toString()) {
                void postSync();
            }
        });
        const testStateChangeSubscription = this.onDidChangeTestStates?.((changedUri) => {
            if (changedUri.toString() === document.uri.toString()) {
                void postSync();
            }
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
                    } satisfies HostMessage);
                }
            } finally {
                isApplyingEdit = false;
            }
            return;
        });

        const runTestSubscription = webviewPanel.webview.onDidReceiveMessage(async (message: WebviewMessage) => {
            if (message.type !== 'runTestFromLine') {
                return;
            }

            const command = message.kind === 'sdoctest' ? 'simple.test.runSdoctest' : 'simple.test.runFile';
            await vscode.commands.executeCommand(command, document.uri);
        });

        const markerSubscription = webviewPanel.webview.onDidReceiveMessage(async (message: WebviewMessage) => {
            if (message.type === 'toggleBreakpointFromLine') {
                await vscode.commands.executeCommand('simple.editor.toggleBreakpoint', document.uri, message.line);
                await postSync();
                return;
            }
            if (message.type === 'toggleBookmarkFromLine') {
                await vscode.commands.executeCommand('simple.editor.toggleBookmark', document.uri, message.line);
                await postSync();
                return;
            }
            if (message.type === 'togglePointerFromLine') {
                await vscode.commands.executeCommand('simple.editor.togglePointer', document.uri, message.line);
                await postSync();
            }
        });

        const navigationSubscription = webviewPanel.webview.onDidReceiveMessage(async (message: WebviewMessage) => {
            if (
                message.type !== 'revealDefinition'
                && message.type !== 'showReferences'
            ) {
                return;
            }

            const documentText = document.getText();
            const offset = message.offset;
            if (offset < 0) {
                return;
            }
            const position = document.positionAt(Math.max(0, Math.min(offset, documentText.length)));

            if (message.type === 'revealDefinition') {
                const rawLocations = await vscode.commands.executeCommand<Array<vscode.Location | vscode.LocationLink>>(
                    'vscode.executeDefinitionProvider',
                    document.uri,
                    position,
                );
                const locations = (rawLocations ?? []).map((item) => item instanceof vscode.Location
                    ? item
                    : new vscode.Location(item.targetUri, item.targetSelectionRange ?? item.targetRange));
                if (locations.length === 0) {
                    return;
                }

                if (locations.length === 1) {
                    await vscode.window.showTextDocument(locations[0].uri, {
                        preview: false,
                        selection: locations[0].range,
                    });
                    return;
                }

                const editor = await vscode.window.showTextDocument(document, {
                    preview: false,
                    selection: new vscode.Range(position, position),
                });
                await vscode.commands.executeCommand('editor.action.goToLocations', editor.document.uri, position, locations, 'goto', 'No definition found');
                return;
            }

            const references = await vscode.commands.executeCommand<vscode.Location[]>(
                'vscode.executeReferenceProvider',
                document.uri,
                position,
            );
            if (!references || references.length === 0) {
                return;
            }

            await vscode.window.showTextDocument(document, {
                preview: false,
                selection: new vscode.Range(position, position),
            });
            await vscode.commands.executeCommand(
                'editor.action.showReferences',
                document.uri,
                position,
                references,
            );
        });

        webviewPanel.onDidDispose(() => {
            changeDocumentSubscription.dispose();
            configurationSubscription.dispose();
            markerChangeSubscription?.dispose();
            testStateChangeSubscription?.dispose();
            messageSubscription.dispose();
            runTestSubscription.dispose();
            markerSubscription.dispose();
            navigationSubscription.dispose();
        });
    }
}
