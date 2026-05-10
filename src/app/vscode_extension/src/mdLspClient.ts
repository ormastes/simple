/**
 * Markdown LSP client — connects to the md_lsp server over stdio.
 */

import * as vscode from 'vscode';
import {
    CloseAction,
    ErrorAction,
    LanguageClient,
    LanguageClientOptions,
    RevealOutputChannelOn,
    ServerOptions,
    TransportKind,
} from 'vscode-languageclient/node';

const MD_SELECTOR: vscode.DocumentSelector = [
    { scheme: 'file', language: 'markdown' },
];

let mdLspClient: LanguageClient | undefined;

export function activateMdLspClient(context: vscode.ExtensionContext): void {
    const outputChannel = vscode.window.createOutputChannel('Simple Markdown LSP', { log: true });
    context.subscriptions.push(outputChannel);

    const serverOptions: ServerOptions = {
        command: 'bin/simple',
        args: ['run', 'src/app/md_lsp/md_lsp_main.spl'],
        transport: TransportKind.stdio,
    };

    const clientOptions: LanguageClientOptions = {
        documentSelector: MD_SELECTOR,
        outputChannel,
        traceOutputChannel: outputChannel,
        revealOutputChannelOn: RevealOutputChannelOn.Never,
        initializationFailedHandler: () => false,
        errorHandler: {
            error: () => ({ action: ErrorAction.Shutdown, handled: true }),
            closed: () => ({ action: CloseAction.DoNotRestart, handled: true }),
        },
    };

    mdLspClient = new LanguageClient(
        'simple-md-lsp',
        'Simple Markdown Language Server',
        serverOptions,
        clientOptions,
    );

    void mdLspClient.start().catch((error) => {
        const detail = error instanceof Error ? error.message : String(error);
        outputChannel.warn(`Markdown LSP failed to start: ${detail}`);
    });

    context.subscriptions.push({
        dispose: () => {
            void mdLspClient?.stop();
            mdLspClient = undefined;
        },
    });
}
