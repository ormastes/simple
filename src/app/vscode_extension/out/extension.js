"use strict";
/**
 * Simple Rich Editor — crash-contained VS Code extension host.
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
Object.defineProperty(exports, "__esModule", { value: true });
exports.activate = activate;
exports.deactivate = deactivate;
const vscode = __importStar(require("vscode"));
const diagnosticsProvider_1 = require("./fallback/diagnosticsProvider");
const semanticTokensProvider_1 = require("./fallback/semanticTokensProvider");
const richCustomEditor_1 = require("./richCustomEditor");
const simpleOutlineProvider_1 = require("./outline/simpleOutlineProvider");
const extensionHostServices_1 = require("./services/extensionHostServices");
const simpleCliService_1 = require("./services/simpleCliService");
const simpleSymbolProviders_1 = require("./symbols/simpleSymbolProviders");
const testCodeLensProvider_1 = require("./testing/testCodeLensProvider");
const testController_1 = require("./testing/testController");
const editorMarkers_1 = require("./testing/editorMarkers");
const testWorkspacePanel_1 = require("./testing/testWorkspacePanel");
const SIMPLE_SELECTOR = [
    { scheme: 'file', language: 'simple' },
    { scheme: 'untitled', language: 'simple' },
];
async function reopenActiveSimpleDocumentWithRichEditor() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        return;
    }
    const document = editor.document;
    const isSimpleFile = document.languageId === 'simple' || document.uri.fsPath.endsWith('.spl');
    if (!isSimpleFile) {
        return;
    }
    await vscode.commands.executeCommand('vscode.openWith', document.uri, richCustomEditor_1.RichCustomEditorProvider.viewType);
}
async function activate(context) {
    const services = new extensionHostServices_1.ExtensionHostServices();
    context.subscriptions.push(services);
    const outlineProvider = new simpleOutlineProvider_1.SimpleOutlineProvider();
    const editorMarkerManager = new editorMarkers_1.EditorMarkerManager();
    let currentOutlineDocument = vscode.window.activeTextEditor?.document;
    const updateOutline = (document) => {
        currentOutlineDocument = document;
        outlineProvider.setActiveDocument(document);
    };
    const cli = new simpleCliService_1.SimpleCliService(services);
    const runCliTestCommand = async (args, resolveFrom) => {
        try {
            await cli.run(args, {
                cwd: vscode.workspace.workspaceFolders?.[0]?.uri.fsPath,
                resolveFrom,
            });
        }
        catch (error) {
            const detail = error instanceof Error ? error.message : String(error);
            void vscode.window.showWarningMessage(`Simple Rich Editor: ${detail}`);
        }
    };
    context.subscriptions.push(vscode.commands.registerCommand('simple.richEditor.showOutputChannel', () => {
        services.showOutputChannel();
    }), vscode.commands.registerCommand('simple.outline.revealSymbol', async (uri, range) => {
        const document = await vscode.workspace.openTextDocument(uri);
        await vscode.window.showTextDocument(document, {
            preview: false,
            selection: range,
        });
    }), vscode.commands.registerCommand('simple.editor.toggleBreakpoint', async (uri, line) => {
        const targetUri = uri ?? vscode.window.activeTextEditor?.document.uri;
        if (!targetUri) {
            return;
        }
        const targetLine = typeof line === 'number'
            ? line
            : vscode.window.activeTextEditor?.selection.active.line;
        if (typeof targetLine !== 'number') {
            return;
        }
        editorMarkerManager.toggleBreakpoint(targetUri, targetLine);
        const active = currentOutlineDocument;
        if (active && active.uri.toString() === targetUri.toString()) {
            updateOutline(active);
        }
    }), vscode.window.registerTreeDataProvider('simpleOutline', outlineProvider), vscode.window.onDidChangeActiveTextEditor((editor) => {
        updateOutline(editor?.document);
    }), vscode.workspace.onDidChangeTextDocument((event) => {
        if (currentOutlineDocument && event.document.uri.toString() === currentOutlineDocument.uri.toString()) {
            updateOutline(event.document);
        }
    }));
    updateOutline(vscode.window.activeTextEditor?.document);
    await services.safeRegister('editor', 'custom editor provider', () => {
        return [
            vscode.window.registerCustomEditorProvider(richCustomEditor_1.RichCustomEditorProvider.viewType, new richCustomEditor_1.RichCustomEditorProvider(context.extensionUri, updateOutline, (documentUri) => editorMarkerManager.getState(documentUri)), {
                webviewOptions: { retainContextWhenHidden: true },
                supportsMultipleEditorsPerDocument: false,
            }),
            vscode.commands.registerCommand('simple.richEditor.open', () => {
                void reopenActiveSimpleDocumentWithRichEditor();
            }),
        ];
    }, context.subscriptions);
    await services.safeRegister('diagnostics', 'fallback diagnostics', () => {
        return new diagnosticsProvider_1.SimpleDiagnosticsProvider();
    }, context.subscriptions);
    await services.safeRegister('semanticTokens', 'fallback semantic tokens', () => {
        return vscode.languages.registerDocumentSemanticTokensProvider(SIMPLE_SELECTOR, new semanticTokensProvider_1.SimpleSemanticTokensProvider(), semanticTokensProvider_1.TOKEN_LEGEND);
    }, context.subscriptions);
    await services.safeRegister('symbols', 'fallback symbol providers', () => {
        return [
            vscode.languages.registerDocumentSymbolProvider(SIMPLE_SELECTOR, new simpleSymbolProviders_1.SimpleDocumentSymbolProvider()),
            vscode.languages.registerWorkspaceSymbolProvider(new simpleSymbolProviders_1.SimpleWorkspaceSymbolProvider()),
            vscode.languages.registerDefinitionProvider(SIMPLE_SELECTOR, new simpleSymbolProviders_1.SimpleDefinitionProvider()),
            vscode.languages.registerHoverProvider(SIMPLE_SELECTOR, new simpleSymbolProviders_1.SimpleHoverProvider()),
        ];
    }, context.subscriptions);
    await services.safeRegister('tests', 'test runner UI', () => {
        const codeLensProvider = new testCodeLensProvider_1.TestCodeLensProvider();
        const testController = new testController_1.SimpleTestController(cli, services);
        return [
            codeLensProvider,
            testController,
            vscode.languages.registerCodeLensProvider(SIMPLE_SELECTOR, codeLensProvider),
            vscode.commands.registerCommand('simple.test.runFile', async (uri) => {
                const target = uri ?? vscode.window.activeTextEditor?.document.uri;
                if (!target) {
                    void vscode.window.showWarningMessage('No Simple file is active');
                    return;
                }
                await runCliTestCommand(['test', target.fsPath], target.fsPath);
            }),
            vscode.commands.registerCommand('simple.test.runSdoctest', async (uri) => {
                const target = uri ?? vscode.window.activeTextEditor?.document.uri;
                if (!target) {
                    void vscode.window.showWarningMessage('No Simple file is active');
                    return;
                }
                await runCliTestCommand(['test', '--sdoctest', target.fsPath], target.fsPath);
            }),
            vscode.commands.registerCommand('simple.test.openWorkspace', () => {
                testWorkspacePanel_1.TestWorkspacePanel.show(context.extensionUri);
            }),
            vscode.commands.registerCommand('simple.test.refreshWorkspace', () => {
                testWorkspacePanel_1.TestWorkspacePanel.currentPanel?.refresh();
            }),
            vscode.commands.registerCommand('simple.test.openLatestArtifacts', () => {
                if (testWorkspacePanel_1.TestWorkspacePanel.currentPanel) {
                    testWorkspacePanel_1.TestWorkspacePanel.currentPanel.openLatestArtifacts();
                }
                else {
                    testWorkspacePanel_1.TestWorkspacePanel.show(context.extensionUri).openLatestArtifacts();
                }
            }),
        ];
    }, context.subscriptions);
    void reopenActiveSimpleDocumentWithRichEditor();
}
function deactivate() { }
//# sourceMappingURL=extension.js.map