/**
 * Simple Rich Editor — crash-contained VS Code extension host.
 */

import * as vscode from 'vscode';
import { SimpleDiagnosticsProvider } from './fallback/diagnosticsProvider';
import { SimpleSemanticTokensProvider, TOKEN_LEGEND } from './fallback/semanticTokensProvider';
import { RichCustomEditorProvider } from './richCustomEditor';
import { SimpleOutlineProvider } from './outline/simpleOutlineProvider';
import { ExtensionHostServices } from './services/extensionHostServices';
import { SimpleCliService } from './services/simpleCliService';
import {
    SimpleDefinitionProvider,
    SimpleDocumentSymbolProvider,
    SimpleHoverProvider,
    SimpleWorkspaceSymbolProvider,
} from './symbols/simpleSymbolProviders';
import { TestCodeLensProvider } from './testing/testCodeLensProvider';
import { SimpleTestController } from './testing/testController';
import { TestWorkspacePanel } from './testing/testWorkspacePanel';

const SIMPLE_SELECTOR: vscode.DocumentSelector = [
    { scheme: 'file', language: 'simple' },
    { scheme: 'untitled', language: 'simple' },
];

async function reopenActiveSimpleDocumentWithRichEditor(): Promise<void> {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        return;
    }

    const document = editor.document;
    const isSimpleFile = document.languageId === 'simple' || document.uri.fsPath.endsWith('.spl');
    if (!isSimpleFile) {
        return;
    }

    await vscode.commands.executeCommand('vscode.openWith', document.uri, RichCustomEditorProvider.viewType);
}

export async function activate(context: vscode.ExtensionContext): Promise<void> {
    const services = new ExtensionHostServices();
    context.subscriptions.push(services);
    const outlineProvider = new SimpleOutlineProvider();
    let currentOutlineDocument = vscode.window.activeTextEditor?.document;
    const updateOutline = (document?: vscode.TextDocument) => {
        currentOutlineDocument = document;
        outlineProvider.setActiveDocument(document);
    };

    const cli = new SimpleCliService(services);
    const runCliTestCommand = async (args: string[]): Promise<void> => {
        try {
            await cli.run(args, { cwd: vscode.workspace.workspaceFolders?.[0]?.uri.fsPath });
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

    await services.safeRegister('editor', 'custom editor provider', () => {
        return [
            vscode.window.registerCustomEditorProvider(
                RichCustomEditorProvider.viewType,
                new RichCustomEditorProvider(context.extensionUri, updateOutline),
                {
                    webviewOptions: { retainContextWhenHidden: true },
                    supportsMultipleEditorsPerDocument: false,
                },
            ),
            vscode.commands.registerCommand('simple.richEditor.open', () => {
                void reopenActiveSimpleDocumentWithRichEditor();
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
            vscode.languages.registerHoverProvider(SIMPLE_SELECTOR, new SimpleHoverProvider()),
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
                await runCliTestCommand(['test', target.fsPath]);
            }),
            vscode.commands.registerCommand('simple.test.runSdoctest', async (uri?: vscode.Uri) => {
                const target = uri ?? vscode.window.activeTextEditor?.document.uri;
                if (!target) {
                    void vscode.window.showWarningMessage('No Simple file is active');
                    return;
                }
                await runCliTestCommand(['test', '--sdoctest', target.fsPath]);
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
        ];
    }, context.subscriptions);

    void reopenActiveSimpleDocumentWithRichEditor();
}

export function deactivate(): void {}
