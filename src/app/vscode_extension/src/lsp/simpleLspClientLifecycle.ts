import * as vscode from 'vscode';
import { spawn, spawnSync } from 'child_process';
import {
    CloseAction,
    ErrorAction,
    LanguageClient,
    LanguageClientOptions,
    RevealOutputChannelOn,
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
            revealOutputChannelOn: RevealOutputChannelOn.Never,
            initializationOptions: request.initializationOptions,
            initializationFailedHandler: () => false,
            errorHandler: {
                error: () => ({ action: ErrorAction.Shutdown, handled: true }),
                closed: () => ({ action: CloseAction.DoNotRestart, handled: true }),
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
                const initializeProbe = await probeInitializeHandshake(request.server.command, request.server.args, request.server.environment);
                if (!initializeProbe.ok) {
                    setFallbackEnabled(true);
                    options.onRunningStateChanged?.(false);
                    options.services.markDegraded(
                        'lsp',
                        'Simple LSP initialize probe failed; fallback providers active',
                        'fallback',
                        initializeProbe.detail,
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

interface LspInitializeProbeResult {
    ok: boolean;
    detail?: string;
}

function createJsonRpcMessage(payload: unknown): string {
    const body = JSON.stringify(payload);
    return `Content-Length: ${Buffer.byteLength(body, 'utf8')}\r\n\r\n${body}`;
}

function tryReadJsonRpcBody(buffer: string): unknown | undefined {
    const marker = '\r\n\r\n';
    const headerEnd = buffer.indexOf(marker);
    if (headerEnd < 0) {
        return undefined;
    }
    const header = buffer.slice(0, headerEnd);
    const match = header.match(/Content-Length:\s*(\d+)/i);
    if (!match) {
        return undefined;
    }
    const contentLength = Number(match[1]);
    const bodyStart = headerEnd + marker.length;
    const body = buffer.slice(bodyStart);
    if (Buffer.byteLength(body, 'utf8') < contentLength) {
        return undefined;
    }
    return JSON.parse(body.slice(0, contentLength));
}

async function probeInitializeHandshake(
    command: string,
    args: string[],
    environment: NodeJS.ProcessEnv,
): Promise<LspInitializeProbeResult> {
    return await new Promise<LspInitializeProbeResult>((resolve) => {
        const child = spawn(command, args, {
            env: environment,
            stdio: 'pipe',
        });
        let settled = false;
        let stdout = '';
        let stderr = '';
        const timeout = setTimeout(() => {
            finish({
                ok: false,
                detail: 'initialize timeout',
            });
        }, 1500);

        const finish = (result: LspInitializeProbeResult): void => {
            if (settled) {
                return;
            }
            settled = true;
            clearTimeout(timeout);
            child.kill('SIGKILL');
            resolve(result);
        };

        child.on('error', (error) => {
            finish({ ok: false, detail: error.message });
        });
        child.on('exit', (code, signal) => {
            if (settled) {
                return;
            }
            finish({
                ok: false,
                detail: [stderr.trim(), stdout.trim()].filter(Boolean).join('\n') || `exit ${code ?? signal ?? 'unknown'}`,
            });
        });
        child.stdout.setEncoding('utf8');
        child.stderr.setEncoding('utf8');
        child.stdout.on('data', (chunk: string) => {
            stdout += chunk;
            try {
                const payload = tryReadJsonRpcBody(stdout) as { error?: { message?: string; code?: number } } | undefined;
                if (!payload) {
                    return;
                }
                if (payload.error) {
                    finish({
                        ok: false,
                        detail: `${payload.error.message ?? 'initialize failed'}${typeof payload.error.code === 'number' ? ` (${payload.error.code})` : ''}`,
                    });
                    return;
                }
                finish({ ok: true });
            } catch (error) {
                finish({
                    ok: false,
                    detail: error instanceof Error ? error.message : String(error),
                });
            }
        });
        child.stderr.on('data', (chunk: string) => {
            stderr += chunk;
        });

        const initializeRequest = createJsonRpcMessage({
            jsonrpc: '2.0',
            id: 1,
            method: 'initialize',
            params: {
                processId: process.pid,
                clientInfo: { name: 'simple-vscode-probe', version: '0.1.0' },
                rootUri: vscode.workspace.workspaceFolders?.[0]?.uri.toString() ?? null,
                capabilities: {},
                workspaceFolders: (vscode.workspace.workspaceFolders ?? []).map((folder) => ({
                    uri: folder.uri.toString(),
                    name: folder.name,
                })),
            },
        });
        child.stdin.write(initializeRequest);
    });
}
