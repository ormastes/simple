import * as vscode from 'vscode';
import { spawnSync } from 'child_process';
import {
    CloseAction,
    ErrorAction,
    LanguageClient,
    LanguageClientOptions,
    ServerOptions,
    State,
    TransportKind,
} from 'vscode-languageclient/node';
import { ExtensionHostServices } from '../services/extensionHostServices';
import { SimpleLspBootstrapHook, SimpleLspBootstrapRequest } from './simpleLspCompatibility';

export interface LspFallbackControls {
    setEnabled(enabled: boolean): void;
}

export interface CreateSimpleLspClientBootstrapOptions {
    services: ExtensionHostServices;
    onRunningStateChanged?: (running: boolean) => void;
    fallbackControls?: LspFallbackControls[];
}

export function createSimpleLspClientBootstrap(
    options: CreateSimpleLspClientBootstrapOptions,
): SimpleLspBootstrapHook {
    return async (request: SimpleLspBootstrapRequest) => {
        const watcher = vscode.workspace.createFileSystemWatcher(request.clientOptions.synchronize.fileEvents);
        const outputChannel = options.services.outputChannel;
        const serverOptions: ServerOptions = {
            command: request.server.command,
            args: request.server.args,
            transport: TransportKind.stdio,
            options: {
                env: request.server.environment,
            },
        };

        const clientOptions: LanguageClientOptions = {
            documentSelector: request.clientOptions.documentSelector as LanguageClientOptions['documentSelector'],
            synchronize: {
                fileEvents: watcher,
            },
            outputChannel,
            traceOutputChannel: outputChannel,
            initializationOptions: request.initializationOptions,
            errorHandler: {
                error: () => ({ action: ErrorAction.Shutdown }),
                closed: () => ({ action: CloseAction.DoNotRestart }),
            },
        };

        const client = new LanguageClient(
            'simple-lsp',
            'Simple Language Server',
            serverOptions,
            clientOptions,
        );

        const setFallbackEnabled = (enabled: boolean): void => {
            for (const control of options.fallbackControls ?? []) {
                control.setEnabled(enabled);
            }
        };

        const syncState = (state: State): void => {
            if (state === State.Running) {
                options.services.markReady('lsp', 'Simple LSP server running', 'native');
                setFallbackEnabled(false);
                options.onRunningStateChanged?.(true);
                return;
            }

            if (state === State.Starting) {
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
            outputChannel.info(`Simple LSP state changed: ${State[event.oldState]} -> ${State[event.newState]}`);
            syncState(event.newState);
        });

        syncState(State.Starting);

        return {
            start: async () => {
                const probe = spawnSync(request.server.command, request.server.args, {
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
                    options.services.markDegraded(
                        'lsp',
                        'Simple LSP command exits immediately; fallback providers active',
                        'fallback',
                        probeOutput || `exit ${probe.status}`,
                    );
                    return;
                }
                try {
                    await client.start();
                } catch (error) {
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
