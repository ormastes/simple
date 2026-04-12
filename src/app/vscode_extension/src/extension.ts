/**
 * Simple Rich Editor — crash-contained VS Code extension host.
 */

import * as vscode from 'vscode';
import { registerSimpleAiSlice } from './ai';
import { SimpleDiagnosticsProvider } from './fallback/diagnosticsProvider';
import { SimpleSemanticTokensProvider, TOKEN_LEGEND } from './fallback/semanticTokensProvider';
import { createSimpleLspCompatibilitySurface } from './lsp';
import { findMathBlockAtPosition, MathPreviewPanel, MathSyncPanel } from './math';
import { SimpleFoldingRangeProvider } from './nativeFoldingProvider';
import { NativeMathProvider } from './nativeMathProvider';
import { RichCustomEditorProvider } from './richCustomEditor';
import { SimpleOutlineProvider } from './outline/simpleOutlineProvider';
import { ExtensionHostServices } from './services/extensionHostServices';
import { SimpleCliService } from './services/simpleCliService';
import {
    SimpleDefinitionProvider,
    SimpleDocumentSymbolProvider,
    SimpleHoverProvider,
    SimpleReferenceProvider,
    SimpleWorkspaceSymbolProvider,
} from './symbols/simpleSymbolProviders';
import { TestCodeLensProvider } from './testing/testCodeLensProvider';
import { SimpleTestController } from './testing/testController';
import { EditorMarkerManager } from './testing/editorMarkers';
import { TestWorkspacePanel } from './testing/testWorkspacePanel';
import { detectTestBlocks } from './testing/testDiscovery';

const SIMPLE_SELECTOR: vscode.DocumentSelector = [
    { scheme: 'file', language: 'simple' },
    { scheme: 'untitled', language: 'simple' },
];

export async function activate(context: vscode.ExtensionContext): Promise<void> {
    const services = new ExtensionHostServices();
    context.subscriptions.push(services);
    const lspSurface = createSimpleLspCompatibilitySurface(context);
    context.subscriptions.push(lspSurface);
    services.markDegraded('lsp', 'Compatibility surface ready; client lifecycle not attached yet', 'fallback');
    const outlineProvider = new SimpleOutlineProvider();
    const editorMarkerManager = new EditorMarkerManager();
    const mathProvider = new NativeMathProvider();
    let currentOutlineDocument = vscode.window.activeTextEditor?.document;
    const updateOutline = (document?: vscode.TextDocument) => {
        currentOutlineDocument = document;
        outlineProvider.setActiveDocument(document);
    };

    const maybeAutoOpenMathSyncPanel = (editor?: vscode.TextEditor): void => {
        if (!editor || editor.document.languageId !== 'simple') {
            return;
        }
        if (!vscode.workspace.getConfiguration('simple.math').get<boolean>('syncPanel.autoOpen', false)) {
            return;
        }
        if (MathSyncPanel.isVisible()) {
            return;
        }
        if (findMathBlockAtPosition(editor.document, editor.selection.active)) {
            MathSyncPanel.show();
        }
    };

    const cli = new SimpleCliService(services);
    const runCliTestCommand = async (args: string[], resolveFrom?: string): Promise<void> => {
        try {
            await cli.run(args, {
                cwd: vscode.workspace.workspaceFolders?.[0]?.uri.fsPath,
                resolveFrom,
            });
        } catch (error) {
            const detail = error instanceof Error ? error.message : String(error);
            void vscode.window.showWarningMessage(`Simple Rich Editor: ${detail}`);
        }
    };

    context.subscriptions.push(
        vscode.commands.registerCommand('simple.richEditor.showOutputChannel', () => {
            services.showOutputChannel();
        }),
        vscode.commands.registerCommand('simple.outline.revealSymbol', async (uri: vscode.Uri, range: vscode.Range) => {
            const document = await vscode.workspace.openTextDocument(uri);
            await vscode.window.showTextDocument(document, {
                preview: false,
                selection: range,
            });
        }),
        vscode.window.registerTreeDataProvider('simpleOutline', outlineProvider),
        vscode.window.onDidChangeActiveTextEditor((editor) => {
            updateOutline(editor?.document);
        }),
        vscode.workspace.onDidChangeTextDocument((event) => {
            if (currentOutlineDocument && event.document.uri.toString() === currentOutlineDocument.uri.toString()) {
                updateOutline(event.document);
            }
        }),
    );
    updateOutline(vscode.window.activeTextEditor?.document);

    await services.safeRegister('lsp', 'LSP compatibility commands', () => {
        return [
            vscode.commands.registerCommand('simple.lsp.showOutputChannel', () => {
                lspSurface.showOutputChannel();
            }),
            vscode.commands.registerCommand('simple.lsp.restart', async () => {
                const result = await lspSurface.restartClient();
                if (!result.ok) {
                    void vscode.window.showWarningMessage(`Simple LSP: ${result.message}`);
                }
            }),
        ];
    }, context.subscriptions);
    services.markDegraded('lsp', 'Compatibility commands ready; no client lifecycle attached', 'fallback');

    await services.safeRegister('editor', 'custom editor provider', () => {
        return [
            vscode.window.registerCustomEditorProvider(
                RichCustomEditorProvider.viewType,
                new RichCustomEditorProvider(
                    context.extensionUri,
                    updateOutline,
                    (documentUri) => editorMarkerManager.getState(documentUri),
                ),
                {
                    webviewOptions: { retainContextWhenHidden: true },
                    supportsMultipleEditorsPerDocument: false,
                },
            ),
            vscode.commands.registerCommand('simple.richEditor.open', () => {
                const editor = vscode.window.activeTextEditor;
                if (!editor) {
                    return;
                }
                void vscode.commands.executeCommand('vscode.openWith', editor.document.uri, RichCustomEditorProvider.viewType);
            }),
        ];
    }, context.subscriptions);

    await services.safeRegister('diagnostics', 'fallback diagnostics', () => {
        return new SimpleDiagnosticsProvider();
    }, context.subscriptions);

    await services.safeRegister('semanticTokens', 'fallback semantic tokens', () => {
        return vscode.languages.registerDocumentSemanticTokensProvider(
            SIMPLE_SELECTOR,
            new SimpleSemanticTokensProvider(),
            TOKEN_LEGEND,
        );
    }, context.subscriptions);

    await services.safeRegister('symbols', 'fallback symbol providers', () => {
        return [
            vscode.languages.registerDocumentSymbolProvider(SIMPLE_SELECTOR, new SimpleDocumentSymbolProvider()),
            vscode.languages.registerWorkspaceSymbolProvider(new SimpleWorkspaceSymbolProvider()),
            vscode.languages.registerDefinitionProvider(SIMPLE_SELECTOR, new SimpleDefinitionProvider()),
            vscode.languages.registerReferenceProvider(SIMPLE_SELECTOR, new SimpleReferenceProvider()),
            vscode.languages.registerHoverProvider(SIMPLE_SELECTOR, new SimpleHoverProvider()),
            vscode.languages.registerHoverProvider(SIMPLE_SELECTOR, mathProvider),
            vscode.languages.registerFoldingRangeProvider(SIMPLE_SELECTOR, new SimpleFoldingRangeProvider()),
            mathProvider,
        ];
    }, context.subscriptions);

    await services.safeRegister('math', 'math preview and sync panels', () => {
        return [
            vscode.commands.registerCommand('simple.math.togglePreview', () => {
                if (MathPreviewPanel.isVisible()) {
                    MathPreviewPanel.close();
                } else {
                    MathPreviewPanel.show();
                }
            }),
            vscode.commands.registerCommand('simple.math.toggleSyncPanel', () => {
                if (MathSyncPanel.isVisible()) {
                    MathSyncPanel.close();
                } else {
                    MathSyncPanel.show();
                }
            }),
            vscode.window.onDidChangeActiveTextEditor((editor) => {
                maybeAutoOpenMathSyncPanel(editor ?? undefined);
            }),
            vscode.window.onDidChangeTextEditorSelection((event) => {
                maybeAutoOpenMathSyncPanel(event.textEditor);
            }),
        ];
    }, context.subscriptions);

    await services.safeRegister('tests', 'test runner UI', () => {
        const codeLensProvider = new TestCodeLensProvider();
        const testController = new SimpleTestController(cli, services);

        return [
            codeLensProvider,
            testController,
            vscode.languages.registerCodeLensProvider(SIMPLE_SELECTOR, codeLensProvider),
            vscode.commands.registerCommand('simple.test.runFile', async (uri?: vscode.Uri) => {
                const target = uri ?? vscode.window.activeTextEditor?.document.uri;
                if (!target) {
                    void vscode.window.showWarningMessage('No Simple file is active');
                    return;
                }
                await runCliTestCommand(['test', target.fsPath], target.fsPath);
            }),
            vscode.commands.registerCommand('simple.test.runAtCursor', async () => {
                const editor = vscode.window.activeTextEditor;
                if (!editor || editor.document.languageId !== 'simple') {
                    void vscode.window.showWarningMessage('No Simple file is active');
                    return;
                }
                const block = detectTestBlocks(editor.document)
                    .filter((candidate) => candidate.line <= editor.selection.active.line)
                    .pop();
                if (block?.kind === 'sdoctest') {
                    await runCliTestCommand(['test', '--sdoctest', editor.document.uri.fsPath], editor.document.uri.fsPath);
                    return;
                }
                await runCliTestCommand(['test', editor.document.uri.fsPath], editor.document.uri.fsPath);
            }),
            vscode.commands.registerCommand('simple.test.runSdoctest', async (uri?: vscode.Uri) => {
                const target = uri ?? vscode.window.activeTextEditor?.document.uri;
                if (!target) {
                    void vscode.window.showWarningMessage('No Simple file is active');
                    return;
                }
                await runCliTestCommand(['test', '--sdoctest', target.fsPath], target.fsPath);
            }),
            vscode.commands.registerCommand('simple.test.openWorkspace', () => {
                TestWorkspacePanel.show(context.extensionUri);
            }),
            vscode.commands.registerCommand('simple.test.refreshWorkspace', () => {
                TestWorkspacePanel.currentPanel?.refresh();
            }),
            vscode.commands.registerCommand('simple.test.openLatestArtifacts', () => {
                if (TestWorkspacePanel.currentPanel) {
                    TestWorkspacePanel.currentPanel.openLatestArtifacts();
                } else {
                    TestWorkspacePanel.show(context.extensionUri).openLatestArtifacts();
                }
            }),
            vscode.commands.registerTextEditorCommand('simple.editor.toggleBreakpoint', (editor, _edit, uri?: vscode.Uri, line?: number) => {
                const targetUri = uri ?? editor.document.uri;
                const targetLine = typeof line === 'number'
                    ? line
                    : editor.selection.active.line;
                if (!targetUri || typeof targetLine !== 'number') {
                    return;
                }
                editorMarkerManager.toggleBreakpoint(targetUri, targetLine);
            }),
            vscode.commands.registerTextEditorCommand('simple.editor.toggleBookmark', (editor, _edit, uri?: vscode.Uri, line?: number) => {
                const targetUri = uri ?? editor.document.uri;
                const targetLine = typeof line === 'number'
                    ? line
                    : editor.selection.active.line;
                if (!targetUri || typeof targetLine !== 'number') {
                    return;
                }
                editorMarkerManager.toggleBookmark(targetUri, targetLine);
            }),
            vscode.commands.registerTextEditorCommand('simple.editor.togglePointer', (editor, _edit, uri?: vscode.Uri, line?: number) => {
                const targetUri = uri ?? editor.document.uri;
                const targetLine = typeof line === 'number'
                    ? line
                    : editor.selection.active.line;
                if (!targetUri || typeof targetLine !== 'number') {
                    return;
                }
                editorMarkerManager.togglePointer(targetUri, targetLine);
            }),
            vscode.commands.registerTextEditorCommand('simple.editor.clearPointer', (editor, _edit, uri?: vscode.Uri) => {
                const targetUri = uri ?? editor.document.uri;
                if (!targetUri) {
                    return;
                }
                editorMarkerManager.clearPointer(targetUri);
            }),
            vscode.commands.registerCommand('simple.editor.nextBookmark', () => {
                const editor = vscode.window.activeTextEditor;
                if (editor) {
                    editorMarkerManager.jumpToNextBookmark(editor);
                }
            }),
            vscode.commands.registerCommand('simple.editor.prevBookmark', () => {
                const editor = vscode.window.activeTextEditor;
                if (editor) {
                    editorMarkerManager.jumpToPreviousBookmark(editor);
                }
            }),
            vscode.commands.registerCommand('simple.math.openCustomEditor', () => {
                const editor = vscode.window.activeTextEditor;
                if (!editor) {
                    return;
                }
                void vscode.commands.executeCommand('vscode.openWith', editor.document.uri, RichCustomEditorProvider.viewType);
            }),
            vscode.commands.registerCommand('simple.math.toggleInlineRender', async () => {
                const config = vscode.workspace.getConfiguration('simple.math');
                const current = config.get<boolean>('renderInline', true);
                await config.update('renderInline', !current, vscode.ConfigurationTarget.Global);
                void vscode.window.showInformationMessage(`Simple inline math rendering ${!current ? 'enabled' : 'disabled'}`);
            }),
        ];
    }, context.subscriptions);

    await services.safeRegister('ai', 'AI feature surface', async () => {
        return registerSimpleAiSlice(context, {
            extensionUri: context.extensionUri,
            documentSelector: SIMPLE_SELECTOR,
        });
    }, context.subscriptions);
}

export function deactivate(): void {}
