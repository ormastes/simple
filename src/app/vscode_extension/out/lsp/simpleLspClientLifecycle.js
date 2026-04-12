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
exports.createSimpleLspClientBootstrap = createSimpleLspClientBootstrap;
const vscode = __importStar(require("vscode"));
const child_process_1 = require("child_process");
const node_1 = require("vscode-languageclient/node");
function createSimpleLspClientBootstrap(options) {
    return async (request) => {
        const watcher = vscode.workspace.createFileSystemWatcher(request.clientOptions.synchronize.fileEvents);
        const outputChannel = options.services.outputChannel;
        const serverOptions = {
            command: request.server.command,
            args: request.server.args,
            transport: node_1.TransportKind.stdio,
            options: {
                env: request.server.environment,
            },
        };
        const clientOptions = {
            documentSelector: request.clientOptions.documentSelector,
            synchronize: {
                fileEvents: watcher,
            },
            outputChannel,
            traceOutputChannel: outputChannel,
            initializationOptions: request.initializationOptions,
            errorHandler: {
                error: () => ({ action: node_1.ErrorAction.Shutdown }),
                closed: () => ({ action: node_1.CloseAction.DoNotRestart }),
            },
        };
        const client = new node_1.LanguageClient('simple-lsp', 'Simple Language Server', serverOptions, clientOptions);
        const setFallbackEnabled = (enabled) => {
            for (const control of options.fallbackControls ?? []) {
                control.setEnabled(enabled);
            }
        };
        const syncState = (state) => {
            if (state === node_1.State.Running) {
                options.services.markReady('lsp', 'Simple LSP server running', 'native');
                setFallbackEnabled(false);
                options.onRunningStateChanged?.(true);
                return;
            }
            if (state === node_1.State.Starting) {
                options.services.setStatus('lsp', {
                    health: 'starting',
                    source: 'native',
                    message: 'Starting Simple LSP server',
                });
                options.onRunningStateChanged?.(false);
                return;
            }
            options.services.markDegraded('lsp', 'Simple LSP unavailable; fallback providers active', 'fallback');
            setFallbackEnabled(true);
            options.onRunningStateChanged?.(false);
        };
        client.onDidChangeState((event) => {
            outputChannel.info(`Simple LSP state changed: ${node_1.State[event.oldState]} -> ${node_1.State[event.newState]}`);
            syncState(event.newState);
        });
        syncState(node_1.State.Starting);
        return {
            start: async () => {
                const probe = (0, child_process_1.spawnSync)(request.server.command, request.server.args, {
                    env: request.server.environment,
                    encoding: 'utf-8',
                    timeout: 500,
                });
                const probeOutput = [probe.stdout, probe.stderr].filter(Boolean).join('\n').trim();
                const exitedQuicklyWithError = probe.status !== null && probe.status !== 0;
                const timedOut = probe.error && 'code' in probe.error && probe.error.code === 'ETIMEDOUT';
                if (exitedQuicklyWithError && !timedOut) {
                    setFallbackEnabled(true);
                    options.onRunningStateChanged?.(false);
                    options.services.markDegraded('lsp', 'Simple LSP command exits immediately; fallback providers active', 'fallback', probeOutput || `exit ${probe.status}`);
                    return;
                }
                try {
                    await client.start();
                }
                catch (error) {
                    setFallbackEnabled(true);
                    options.onRunningStateChanged?.(false);
                    const detail = error instanceof Error ? error.stack ?? error.message : String(error);
                    options.services.markDegraded('lsp', 'Failed to start Simple LSP server; fallback providers active', 'fallback', detail);
                    throw error;
                }
            },
            restart: async () => {
                await client.restart();
            },
            stop: async () => {
                setFallbackEnabled(true);
                options.onRunningStateChanged?.(false);
                await client.stop();
            },
            dispose: async () => {
                setFallbackEnabled(true);
                options.onRunningStateChanged?.(false);
                watcher.dispose();
                await client.stop();
            },
        };
    };
}
//# sourceMappingURL=simpleLspClientLifecycle.js.map