"use strict";
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
const node_1 = require("vscode-languageclient/node");
const languageModelClient_1 = require("./ai/languageModelClient");
const chatPanel_1 = require("./ai/chatPanel");
const inlineCompletionProvider_1 = require("./ai/inlineCompletionProvider");
const environmentDetector_1 = require("./wasm/environmentDetector");
const wasmLspBridge_1 = require("./wasm/wasmLspBridge");
const math_1 = require("./math");
/** Path to bundled WASM LSP binary (relative to extension root) */
const WASM_LSP_PATH = 'wasm/simple-lsp.wasm';
let client;
let statusBarItem;
let aiStatusBarItem;
let outputChannel;
let aiOutputChannel;
let lmClient;
let inlineCompletionProvider;
/** Whether the LSP is running via WASM (true) or native subprocess (false) */
let usingWasmLsp = false;
/** Callback to notify math hover provider of LSP state changes */
let setMathLspRunning;
function activate(context) {
    console.log('Simple Language extension activating...');
    // Create output channel for LSP communication
    outputChannel = vscode.window.createOutputChannel('Simple Language Server');
    context.subscriptions.push(outputChannel);
    // Create output channel for AI features
    aiOutputChannel = vscode.window.createOutputChannel('Simple AI Assistant');
    context.subscriptions.push(aiOutputChannel);
    // Log environment info
    outputChannel.appendLine((0, environmentDetector_1.getEnvironmentDescription)());
    // Start LSP (async - determines native vs WASM)
    startLspClient(context).then(() => {
        // Initialize AI features after LSP is set up
        initializeAI(context);
    });
    // Initialize math block rendering features.
    // Pass LSP state callback so the math hover provider can defer to the
    // LSP hover handler (src/app/lsp/handlers/hover.spl) when connected.
    (0, math_1.activateMathFeatures)(context, (setter) => {
        setMathLspRunning = setter;
    });
    console.log('Simple Language extension activated');
}
/**
 * Create server options based on environment (native subprocess or WASM in-process).
 *
 * Selection logic:
 * - `simple.lsp.mode = "native"` -> always native subprocess
 * - `simple.lsp.mode = "wasm"` -> always WASM (fail if not available)
 * - `simple.lsp.mode = "auto"` (default) -> WASM on web, native on desktop
 */
async function createServerOptions(context) {
    const useWasm = (0, environmentDetector_1.shouldUseWasm)();
    if (useWasm) {
        // Try WASM LSP
        const wasmAvailable = await (0, wasmLspBridge_1.isWasmLspAvailable)(context, WASM_LSP_PATH);
        if (wasmAvailable) {
            const wasmOptions = await (0, wasmLspBridge_1.createWasmServerOptions)({
                wasmPath: WASM_LSP_PATH,
                context,
                outputChannel: outputChannel,
            });
            if (wasmOptions) {
                usingWasmLsp = true;
                outputChannel?.appendLine('Using WASM LSP server (in-process)');
                return wasmOptions;
            }
        }
        outputChannel?.appendLine('WASM LSP not available, falling back to native');
    }
    // Native subprocess (default)
    usingWasmLsp = false;
    const config = vscode.workspace.getConfiguration('simple');
    const serverPath = config.get('lsp.serverPath', 'simple');
    outputChannel?.appendLine(`Using native LSP server: ${serverPath} lsp`);
    return {
        command: serverPath,
        args: ['lsp'],
        transport: node_1.TransportKind.stdio,
        options: {
            env: process.env
        }
    };
}
async function startLspClient(context) {
    const config = vscode.workspace.getConfiguration('simple');
    // Create server options (native or WASM)
    const serverOptions = await createServerOptions(context);
    // Client options
    const clientOptions = {
        // Register for .spl files
        documentSelector: [
            { scheme: 'file', language: 'simple' },
            { scheme: 'untitled', language: 'simple' },
            // Support vscode-vfs scheme for web environments
            { scheme: 'vscode-vfs', language: 'simple' }
        ],
        // Synchronize file watching
        synchronize: {
            // Watch .spl files
            fileEvents: vscode.workspace.createFileSystemWatcher('**/*.spl')
        },
        // Output channel for LSP logs
        outputChannel: outputChannel,
        // Trace level (off, messages, verbose)
        traceOutputChannel: outputChannel,
        // Initialize options
        initializationOptions: {
            semanticTokens: config.get('lsp.enableSemanticTokens', true),
            inlayHints: config.get('lsp.enableInlayHints', true),
            codeActions: config.get('lsp.enableCodeActions', true),
            pullDiagnostics: config.get('lsp.enablePullDiagnostics', true),
            debounceDelay: config.get('lsp.debounceDelay', 300),
            wasmMode: usingWasmLsp,
        }
    };
    // Create LSP client
    client = new node_1.LanguageClient('simple-lsp', 'Simple Language Server', serverOptions, clientOptions);
    // Setup status bar
    setupStatusBar(context);
    // Register commands
    registerCommands(context);
    // Start LSP client
    client.start().then(() => {
        updateStatusBar(node_1.State.Running);
        setMathLspRunning?.(true);
        const mode = usingWasmLsp ? '(WASM)' : '(native)';
        outputChannel?.appendLine(`Simple LSP server started successfully ${mode}`);
    }).catch((error) => {
        updateStatusBar(node_1.State.Stopped);
        setMathLspRunning?.(false);
        outputChannel?.appendLine(`Failed to start LSP server: ${error}`);
        vscode.window.showErrorMessage(`Failed to start Simple LSP server. Check output for details.`, 'Show Output').then(selection => {
            if (selection === 'Show Output') {
                outputChannel?.show();
            }
        });
    });
    // Monitor client state changes
    client.onDidChangeState((event) => {
        outputChannel?.appendLine(`LSP state changed: ${node_1.State[event.oldState]} -> ${node_1.State[event.newState]}`);
        updateStatusBar(event.newState);
        // Notify math hover provider of LSP state so it can defer to the
        // LSP hover handler (src/app/lsp/handlers/hover.spl) when connected
        setMathLspRunning?.(event.newState === node_1.State.Running);
    });
}
async function initializeAI(context) {
    const config = vscode.workspace.getConfiguration('simple');
    const aiEnabled = config.get('ai.enabled', true);
    if (!aiEnabled) {
        aiOutputChannel?.appendLine('AI features disabled by configuration');
        return;
    }
    // Initialize language model client
    lmClient = new languageModelClient_1.LanguageModelClient(aiOutputChannel);
    await lmClient.initialize();
    if (!lmClient.isAvailable()) {
        aiOutputChannel?.appendLine('WARNING: No language models available. Install GitHub Copilot or compatible extension.');
        vscode.window.showWarningMessage('Simple AI features require GitHub Copilot or compatible language model extension.', 'Install Copilot').then(selection => {
            if (selection === 'Install Copilot') {
                vscode.env.openExternal(vscode.Uri.parse('vscode:extension/GitHub.copilot'));
            }
        });
    }
    // Setup AI status bar
    setupAIStatusBar(context);
    // Register AI commands
    registerAICommands(context);
    // Register inline completion provider (if enabled)
    const inlineCompletionsEnabled = config.get('ai.inlineCompletions', true);
    if (inlineCompletionsEnabled && lmClient.isAvailable()) {
        inlineCompletionProvider = new inlineCompletionProvider_1.AIInlineCompletionProvider(lmClient);
        context.subscriptions.push(vscode.languages.registerInlineCompletionItemProvider({ scheme: 'file', language: 'simple' }, inlineCompletionProvider));
        aiOutputChannel?.appendLine('Inline completions enabled');
    }
    aiOutputChannel?.appendLine('AI features initialized');
}
function setupAIStatusBar(context) {
    // Create AI status bar item
    aiStatusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 99);
    aiStatusBarItem.command = 'simple.ai.toggleInlineCompletions';
    aiStatusBarItem.show();
    context.subscriptions.push(aiStatusBarItem);
    updateAIStatusBar();
}
function updateAIStatusBar() {
    if (!aiStatusBarItem)
        return;
    const isAvailable = lmClient?.isAvailable() ?? false;
    const isEnabled = inlineCompletionProvider?.isEnabled() ?? false;
    if (!isAvailable) {
        aiStatusBarItem.text = '$(warning) AI';
        aiStatusBarItem.tooltip = 'AI features unavailable (install GitHub Copilot)';
        aiStatusBarItem.backgroundColor = new vscode.ThemeColor('statusBarItem.warningBackground');
    }
    else if (isEnabled) {
        aiStatusBarItem.text = '$(sparkle) AI';
        aiStatusBarItem.tooltip = 'AI completions enabled (click to disable)';
        aiStatusBarItem.backgroundColor = undefined;
    }
    else {
        aiStatusBarItem.text = '$(circle-slash) AI';
        aiStatusBarItem.tooltip = 'AI completions disabled (click to enable)';
        aiStatusBarItem.backgroundColor = undefined;
    }
}
function registerAICommands(context) {
    // Open AI chat panel
    context.subscriptions.push(vscode.commands.registerCommand('simple.ai.openChat', () => {
        if (!lmClient) {
            vscode.window.showErrorMessage('AI features not initialized');
            return;
        }
        chatPanel_1.ChatPanel.show(context.extensionUri, lmClient);
    }));
    // Toggle inline completions
    context.subscriptions.push(vscode.commands.registerCommand('simple.ai.toggleInlineCompletions', () => {
        if (!inlineCompletionProvider) {
            vscode.window.showErrorMessage('Inline completions not available');
            return;
        }
        const newState = !inlineCompletionProvider.isEnabled();
        inlineCompletionProvider.setEnabled(newState);
        updateAIStatusBar();
        const message = newState
            ? 'AI inline completions enabled'
            : 'AI inline completions disabled';
        vscode.window.showInformationMessage(message);
    }));
    // Explain selected code
    context.subscriptions.push(vscode.commands.registerCommand('simple.ai.explainCode', async () => {
        const editor = vscode.window.activeTextEditor;
        if (!editor) {
            vscode.window.showErrorMessage('No active editor');
            return;
        }
        const selection = editor.selection;
        const code = editor.document.getText(selection);
        if (!code.trim()) {
            vscode.window.showErrorMessage('No code selected');
            return;
        }
        if (!lmClient) {
            vscode.window.showErrorMessage('AI features not initialized');
            return;
        }
        try {
            const explanation = await vscode.window.withProgress({
                location: vscode.ProgressLocation.Notification,
                title: 'Explaining code...',
                cancellable: true
            }, async (progress, token) => {
                return await lmClient.explain(code, editor.document.languageId);
            });
            // Show explanation in new editor
            const doc = await vscode.workspace.openTextDocument({
                content: `# Code Explanation\n\n${explanation}`,
                language: 'markdown'
            });
            await vscode.window.showTextDocument(doc, vscode.ViewColumn.Beside);
        }
        catch (error) {
            vscode.window.showErrorMessage(`Failed to explain code: ${error.message}`);
        }
    }));
    // Review selected code
    context.subscriptions.push(vscode.commands.registerCommand('simple.ai.reviewCode', async () => {
        const editor = vscode.window.activeTextEditor;
        if (!editor) {
            vscode.window.showErrorMessage('No active editor');
            return;
        }
        const selection = editor.selection;
        const code = editor.document.getText(selection);
        if (!code.trim()) {
            vscode.window.showErrorMessage('No code selected');
            return;
        }
        if (!lmClient) {
            vscode.window.showErrorMessage('AI features not initialized');
            return;
        }
        try {
            const review = await vscode.window.withProgress({
                location: vscode.ProgressLocation.Notification,
                title: 'Reviewing code...',
                cancellable: true
            }, async (progress, token) => {
                return await lmClient.review(code, editor.document.languageId);
            });
            // Show review in new editor
            const doc = await vscode.workspace.openTextDocument({
                content: `# Code Review\n\n${review}`,
                language: 'markdown'
            });
            await vscode.window.showTextDocument(doc, vscode.ViewColumn.Beside);
        }
        catch (error) {
            vscode.window.showErrorMessage(`Failed to review code: ${error.message}`);
        }
    }));
    // Generate code from description
    context.subscriptions.push(vscode.commands.registerCommand('simple.ai.generateCode', async () => {
        const description = await vscode.window.showInputBox({
            prompt: 'Describe the code you want to generate',
            placeHolder: 'e.g., "a function that sorts a list of numbers"'
        });
        if (!description) {
            return;
        }
        if (!lmClient) {
            vscode.window.showErrorMessage('AI features not initialized');
            return;
        }
        try {
            const code = await vscode.window.withProgress({
                location: vscode.ProgressLocation.Notification,
                title: 'Generating code...',
                cancellable: true
            }, async (progress, token) => {
                return await lmClient.generate(description, 'simple');
            });
            // Insert generated code at cursor
            const editor = vscode.window.activeTextEditor;
            if (editor) {
                await editor.edit(editBuilder => {
                    editBuilder.insert(editor.selection.active, code);
                });
            }
        }
        catch (error) {
            vscode.window.showErrorMessage(`Failed to generate code: ${error.message}`);
        }
    }));
    // Completion accepted event (for telemetry/logging)
    context.subscriptions.push(vscode.commands.registerCommand('simple.ai.completionAccepted', () => {
        aiOutputChannel?.appendLine('AI completion accepted');
    }));
}
function deactivate() {
    if (!client) {
        return undefined;
    }
    outputChannel?.appendLine('Stopping Simple LSP server...');
    return client.stop().then(() => {
        outputChannel?.appendLine('Simple LSP server stopped');
    });
}
function setupStatusBar(context) {
    // Create status bar item
    statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 100);
    statusBarItem.command = 'simple.lsp.showOutputChannel';
    statusBarItem.show();
    context.subscriptions.push(statusBarItem);
    updateStatusBar(node_1.State.Starting);
}
function updateStatusBar(state) {
    if (!statusBarItem)
        return;
    const modeLabel = usingWasmLsp ? ' (WASM)' : '';
    switch (state) {
        case node_1.State.Running:
            statusBarItem.text = '$(check) Simple' + modeLabel;
            statusBarItem.tooltip = `Simple LSP Server: Running${modeLabel}`;
            statusBarItem.backgroundColor = undefined;
            break;
        case node_1.State.Starting:
            statusBarItem.text = '$(sync~spin) Simple';
            statusBarItem.tooltip = 'Simple LSP Server: Starting...';
            statusBarItem.backgroundColor = undefined;
            break;
        case node_1.State.Stopped:
            statusBarItem.text = '$(error) Simple';
            statusBarItem.tooltip = 'Simple LSP Server: Stopped';
            statusBarItem.backgroundColor = new vscode.ThemeColor('statusBarItem.errorBackground');
            break;
    }
}
function registerCommands(context) {
    // Restart LSP server command
    context.subscriptions.push(vscode.commands.registerCommand('simple.lsp.restart', async () => {
        if (client) {
            outputChannel?.appendLine('Restarting Simple LSP server...');
            await client.restart();
            vscode.window.showInformationMessage('Simple LSP server restarted');
        }
    }));
    // Show output channel command
    context.subscriptions.push(vscode.commands.registerCommand('simple.lsp.showOutputChannel', () => {
        outputChannel?.show();
    }));
    // Configuration change handler
    context.subscriptions.push(vscode.workspace.onDidChangeConfiguration((event) => {
        if (event.affectsConfiguration('simple.lsp')) {
            vscode.window.showInformationMessage('Simple LSP configuration changed. Restart required.', 'Restart Now').then(selection => {
                if (selection === 'Restart Now') {
                    vscode.commands.executeCommand('simple.lsp.restart');
                }
            });
        }
    }));
}
//# sourceMappingURL=extension.js.map