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
exports.createSimpleBrowserLspController = createSimpleBrowserLspController;
const vscode = __importStar(require("vscode"));
const browser_1 = require("vscode-languageclient/browser");
const simpleLspServerResolver_1 = require("../services/simpleLspServerResolver");
const wasmLspBridge_1 = require("../wasm/wasmLspBridge");
const simpleLspCapabilityReceipt_1 = require("./simpleLspCapabilityReceipt");
const WASM_LSP_PATH = 'wasm/simple-lsp.wasm';
function readConfiguration() {
    const config = vscode.workspace.getConfiguration('simple');
    const rawMode = config.get('lsp.mode', 'auto');
    return {
        mode: rawMode === 'native' || rawMode === 'wasm' ? rawMode : 'auto',
        enableSemanticTokens: config.get('lsp.enableSemanticTokens', true),
        enableInlayHints: config.get('lsp.enableInlayHints', true),
        enableCodeActions: config.get('lsp.enableCodeActions', true),
        enablePullDiagnostics: config.get('lsp.enablePullDiagnostics', true),
        debounceDelay: config.get('lsp.debounceDelay', 300),
    };
}
function createSimpleBrowserLspController(options) {
    const outputChannel = vscode.window.createOutputChannel('Simple LSP Compatibility', { log: true });
    const watcher = vscode.workspace.createFileSystemWatcher('**/*.spl');
    let client;
    const setFallbackEnabled = (enabled) => {
        for (const control of options.fallbackControls ?? []) {
            control.setEnabled(enabled);
        }
    };
    const syncState = (state) => {
        if (state === browser_1.State.Running) {
            (0, simpleLspCapabilityReceipt_1.publishLspCapabilityReceipt)(options.services, options.fallbackControls ?? [], (0, simpleLspCapabilityReceipt_1.authoritativeLspReceipt)('wasm'));
            return;
        }
        if (state === browser_1.State.Starting) {
            options.services.setStatus('lsp', {
                health: 'starting',
                source: 'wasm',
                message: 'Starting Simple LSP server (wasm)',
            });
            return;
        }
        (0, simpleLspCapabilityReceipt_1.publishLspCapabilityReceipt)(options.services, options.fallbackControls ?? [], (0, simpleLspCapabilityReceipt_1.degradedLspReceipt)('Simple LSP unavailable'));
    };
    const bootstrapClient = async () => {
        const configuration = readConfiguration();
        if (configuration.mode === 'native') {
            const receipt = (0, simpleLspCapabilityReceipt_1.degradedLspReceipt)('Native LSP mode is not supported in browser hosts');
            (0, simpleLspCapabilityReceipt_1.publishLspCapabilityReceipt)(options.services, options.fallbackControls ?? [], receipt);
            return {
                ok: false,
                message: receipt.message,
            };
        }
        const wasmAvailable = await (0, wasmLspBridge_1.isWasmLspAvailable)(options.context, WASM_LSP_PATH);
        if (!wasmAvailable) {
            const receipt = (0, simpleLspCapabilityReceipt_1.degradedLspReceipt)('Simple LSP WASM artifact is unavailable', `Expected ${WASM_LSP_PATH}`);
            (0, simpleLspCapabilityReceipt_1.publishLspCapabilityReceipt)(options.services, options.fallbackControls ?? [], receipt);
            return {
                ok: false,
                message: receipt.message,
                detail: receipt.detail,
            };
        }
        const wasmOptions = await (0, wasmLspBridge_1.createWasmServerOptions)({
            wasmPath: WASM_LSP_PATH,
            context: options.context,
            outputChannel,
        });
        if (!wasmOptions.serverOptions) {
            const receipt = (0, simpleLspCapabilityReceipt_1.degradedLspReceipt)('Simple LSP WASM runtime is unavailable', wasmOptions.detail);
            (0, simpleLspCapabilityReceipt_1.publishLspCapabilityReceipt)(options.services, options.fallbackControls ?? [], receipt);
            return {
                ok: false,
                message: receipt.message,
                detail: receipt.detail,
            };
        }
        const clientOptions = {
            documentSelector: (0, simpleLspServerResolver_1.createSimpleLspDocumentSelector)(),
            synchronize: {
                fileEvents: watcher,
            },
            outputChannel,
            traceOutputChannel: outputChannel,
            revealOutputChannelOn: browser_1.RevealOutputChannelOn.Never,
            initializationOptions: {
                semanticTokens: configuration.enableSemanticTokens,
                inlayHints: configuration.enableInlayHints,
                codeActions: configuration.enableCodeActions,
                pullDiagnostics: configuration.enablePullDiagnostics,
                debounceDelay: configuration.debounceDelay,
                wasmMode: true,
            },
            initializationFailedHandler: () => false,
            errorHandler: {
                error: () => ({ action: browser_1.ErrorAction.Shutdown, handled: true }),
                closed: () => ({ action: browser_1.CloseAction.DoNotRestart, handled: true }),
            },
        };
        client = new browser_1.LanguageClient('simple-lsp', 'Simple Language Server', wasmOptions.serverOptions, clientOptions);
        client.onDidChangeState((event) => {
            outputChannel.info(`Simple LSP state changed: ${browser_1.State[event.oldState]} -> ${browser_1.State[event.newState]}`);
            syncState(event.newState);
        });
        syncState(browser_1.State.Starting);
        try {
            await client.start();
            return {
                ok: true,
                message: 'LSP client bootstrap completed.',
            };
        }
        catch (error) {
            const detail = error instanceof Error ? error.stack ?? error.message : String(error);
            const receipt = (0, simpleLspCapabilityReceipt_1.degradedLspReceipt)('Failed to start Simple LSP server', detail);
            (0, simpleLspCapabilityReceipt_1.publishLspCapabilityReceipt)(options.services, options.fallbackControls ?? [], receipt);
            return {
                ok: false,
                message: receipt.message,
                detail: receipt.detail,
            };
        }
    };
    return {
        async bootstrapClient() {
            return bootstrapClient();
        },
        async restartClient() {
            if (!client) {
                return bootstrapClient();
            }
            try {
                await client.stop();
                client = undefined;
                return bootstrapClient();
            }
            catch (error) {
                const detail = error instanceof Error ? error.stack ?? error.message : String(error);
                const receipt = (0, simpleLspCapabilityReceipt_1.degradedLspReceipt)('Failed to restart attached LSP client', detail);
                (0, simpleLspCapabilityReceipt_1.publishLspCapabilityReceipt)(options.services, options.fallbackControls ?? [], receipt);
                return {
                    ok: false,
                    message: receipt.message,
                    detail: receipt.detail,
                };
            }
        },
        showOutputChannel() {
            outputChannel.show(true);
        },
        dispose() {
            setFallbackEnabled(true);
            watcher.dispose();
            void client?.stop();
            outputChannel.dispose();
        },
    };
}
//# sourceMappingURL=simpleLspBrowserLifecycle.js.map