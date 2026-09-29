import * as vscode from 'vscode';
import {
    CloseAction,
    ErrorAction,
    LanguageClient,
    RevealOutputChannelOn,
    State,
} from 'vscode-languageclient/browser';
import { ExtensionHostServices } from '../services/extensionHostServices';
import { createSimpleLspDocumentSelector } from '../services/simpleLspServerResolver';
import { createWasmServerOptions, isWasmLspAvailable } from '../wasm/wasmLspBridge';
import {
    authoritativeLspReceipt,
    degradedLspReceipt,
    publishLspCapabilityReceipt,
    SimpleLspFallbackControl,
} from './simpleLspCapabilityReceipt';

const WASM_LSP_PATH = 'wasm/simple-lsp.wasm';

export interface BrowserLspOperationResult {
    ok: boolean;
    message: string;
    detail?: string;
}

export interface CreateSimpleBrowserLspControllerOptions {
    context: vscode.ExtensionContext;
    services: ExtensionHostServices;
    fallbackControls?: SimpleLspFallbackControl[];
}

function readConfiguration(): {
    mode: 'auto' | 'native' | 'wasm';
    enableSemanticTokens: boolean;
    enableInlayHints: boolean;
    enableCodeActions: boolean;
    enablePullDiagnostics: boolean;
    debounceDelay: number;
} {
    const config = vscode.workspace.getConfiguration('simple');
    const rawMode = config.get<string>('lsp.mode', 'auto');
    return {
        mode: rawMode === 'native' || rawMode === 'wasm' ? rawMode : 'auto',
        enableSemanticTokens: config.get<boolean>('lsp.enableSemanticTokens', true),
        enableInlayHints: config.get<boolean>('lsp.enableInlayHints', true),
        enableCodeActions: config.get<boolean>('lsp.enableCodeActions', true),
        enablePullDiagnostics: config.get<boolean>('lsp.enablePullDiagnostics', true),
        debounceDelay: config.get<number>('lsp.debounceDelay', 300),
    };
}

export interface SimpleBrowserLspController extends vscode.Disposable {
    bootstrapClient(): Promise<BrowserLspOperationResult>;
    restartClient(): Promise<BrowserLspOperationResult>;
    showOutputChannel(): void;
}

export function createSimpleBrowserLspController(
    options: CreateSimpleBrowserLspControllerOptions,
): SimpleBrowserLspController {
    const outputChannel = vscode.window.createOutputChannel('Simple LSP Compatibility', { log: true });
    const watcher = vscode.workspace.createFileSystemWatcher('**/*.spl');
    let client: LanguageClient | undefined;

    const setFallbackEnabled = (enabled: boolean): void => {
        for (const control of options.fallbackControls ?? []) {
            control.setEnabled(enabled);
        }
    };

    const syncState = (state: State): void => {
        if (state === State.Running) {
            publishLspCapabilityReceipt(options.services, options.fallbackControls ?? [], authoritativeLspReceipt('wasm'));
            return;
        }

        if (state === State.Starting) {
            options.services.setStatus('lsp', {
                health: 'starting',
                source: 'wasm',
                message: 'Starting Simple LSP server (wasm)',
            });
            return;
        }

        publishLspCapabilityReceipt(options.services, options.fallbackControls ?? [], degradedLspReceipt('Simple LSP unavailable'));
    };

    const bootstrapClient = async (): Promise<BrowserLspOperationResult> => {
        const configuration = readConfiguration();
        if (configuration.mode === 'native') {
            const receipt = degradedLspReceipt('Native LSP mode is not supported in browser hosts');
            publishLspCapabilityReceipt(options.services, options.fallbackControls ?? [], receipt);
            return {
                ok: false,
                message: receipt.message,
            };
        }

        const wasmAvailable = await isWasmLspAvailable(options.context, WASM_LSP_PATH);
        if (!wasmAvailable) {
            const receipt = degradedLspReceipt('Simple LSP WASM artifact is unavailable', `Expected ${WASM_LSP_PATH}`);
            publishLspCapabilityReceipt(options.services, options.fallbackControls ?? [], receipt);
            return {
                ok: false,
                message: receipt.message,
                detail: receipt.detail,
            };
        }

        const wasmOptions = await createWasmServerOptions({
            wasmPath: WASM_LSP_PATH,
            context: options.context,
            outputChannel,
        });
        if (!wasmOptions.serverOptions) {
            const receipt = degradedLspReceipt('Simple LSP WASM runtime is unavailable', wasmOptions.detail);
            publishLspCapabilityReceipt(options.services, options.fallbackControls ?? [], receipt);
            return {
                ok: false,
                message: receipt.message,
                detail: receipt.detail,
            };
        }

        const clientOptions = {
            documentSelector: createSimpleLspDocumentSelector() as never,
            synchronize: {
                fileEvents: watcher,
            },
            outputChannel,
            traceOutputChannel: outputChannel,
            revealOutputChannelOn: RevealOutputChannelOn.Never,
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
                error: () => ({ action: ErrorAction.Shutdown, handled: true }),
                closed: () => ({ action: CloseAction.DoNotRestart, handled: true }),
            },
        };

        client = new LanguageClient(
            'simple-lsp',
            'Simple Language Server',
            wasmOptions.serverOptions as never,
            clientOptions,
        );
        client.onDidChangeState((event) => {
            outputChannel.info(`Simple LSP state changed: ${State[event.oldState]} -> ${State[event.newState]}`);
            syncState(event.newState);
        });
        syncState(State.Starting);

        try {
            await client.start();
            return {
                ok: true,
                message: 'LSP client bootstrap completed.',
            };
        } catch (error) {
            const detail = error instanceof Error ? error.stack ?? error.message : String(error);
            const receipt = degradedLspReceipt('Failed to start Simple LSP server', detail);
            publishLspCapabilityReceipt(options.services, options.fallbackControls ?? [], receipt);
            return {
                ok: false,
                message: receipt.message,
                detail: receipt.detail,
            };
        }
    };

    return {
        async bootstrapClient(): Promise<BrowserLspOperationResult> {
            return bootstrapClient();
        },
        async restartClient(): Promise<BrowserLspOperationResult> {
            if (!client) {
                return bootstrapClient();
            }
            try {
                await client.stop();
                client = undefined;
                return bootstrapClient();
            } catch (error) {
                const detail = error instanceof Error ? error.stack ?? error.message : String(error);
                const receipt = degradedLspReceipt('Failed to restart attached LSP client', detail);
                publishLspCapabilityReceipt(options.services, options.fallbackControls ?? [], receipt);
                return {
                    ok: false,
                    message: receipt.message,
                    detail: receipt.detail,
                };
            }
        },
        showOutputChannel(): void {
            outputChannel.show(true);
        },
        dispose(): void {
            setFallbackEnabled(true);
            watcher.dispose();
            void client?.stop();
            outputChannel.dispose();
        },
    };
}
