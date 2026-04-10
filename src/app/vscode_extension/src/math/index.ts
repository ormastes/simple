/**
 * Math module barrel export and activation
 *
 * Provides math block rendering, preview, and hover features
 * for Simple language `m{ ... }` math blocks.
 *
 * The existing Simple rendering infrastructure:
 *   src/lib/math_repr.spl    - Math expression parser with to_pretty(), render_latex_raw(), to_md()
 *   src/lib/mathjax.spl      - MathJax SFFI wrapper for SVG/HTML rendering
 *   src/app/cli/query_visibility.spl - query/LSP hover path that renders math blocks server-side
 *   src/app/lsp/             - Full LSP server with hover, completion, diagnostics, etc.
 *
 * This module provides local TypeScript equivalents (via mathConverter.ts) for
 * quick inline preview and fallback hover when the LSP is not connected.
 */

import * as vscode from 'vscode';
import * as path from 'path';
import { MathDecorationProvider } from './mathDecorationProvider';
import { MathCoreWasmBridge } from './mathCoreWasm';
import { MathPreviewPanel } from './mathPreviewPanel';
import { MathSyncPanel } from './mathSyncPanel';
import { MathHoverProvider } from './mathHoverProvider';

export { MathDecorationProvider } from './mathDecorationProvider';
export { MathCoreWasmBridge } from './mathCoreWasm';
export { MathPreviewPanel } from './mathPreviewPanel';
export { MathSyncPanel } from './mathSyncPanel';
export { MathHoverProvider } from './mathHoverProvider';
export { simpleToLatex, simpleToUnicode } from './mathConverter';

/**
 * Activate all math-related features and register providers.
 * Call this from the main extension activate() function.
 *
 * @param context - Extension context
 * @param onLspStateChanged - Optional callback that receives a function to update
 *   LSP running state. When the LSP is running, the hover provider defers to
 *   the query/LSP hover path which provides
 *   full math rendering.
 */
export function activateMathFeatures(
    context: vscode.ExtensionContext,
    onLspStateChanged?: (setLspRunning: (running: boolean) => void) => void,
    debugLogger?: (message: string) => void,
): void {
    const config = vscode.workspace.getConfiguration('simple');

    // Check if math features are enabled
    if (!config.get<boolean>('math.enabled', true)) {
        return;
    }

    // Create the shared decoration provider
    const decorationProvider = new MathDecorationProvider(debugLogger);
    context.subscriptions.push(decorationProvider);

    // Initialize optional math-core WASM bridge. Until the Simple-side ABI is
    // exported, this stays in graceful fallback mode and hover uses the local
    // TypeScript converter.
    const mathCoreBridge = new MathCoreWasmBridge();
    void mathCoreBridge.initialize(context.extensionUri);

    // Set up SVG cache directory for inline math rendering
    const svgCacheDir = path.join(context.globalStorageUri.fsPath, 'math-svg-cache');
    decorationProvider.setSvgCacheDir(svgCacheDir);

    // Set initial inline rendering state from config
    const inlineEnabled = config.get<boolean>('math.renderInline', true);
    decorationProvider.setEnabled(inlineEnabled);

    // Register hover provider (acts as fallback when LSP is not connected)
    const hoverProvider = new MathHoverProvider(decorationProvider, mathCoreBridge);

    // Expose LSP state setter so the extension can notify when LSP starts/stops.
    // When LSP is running, the hover handler in src/app/lsp/handlers/hover.spl
    // provides full rendering and this provider defers to it.
    if (onLspStateChanged) {
        onLspStateChanged((running: boolean) => hoverProvider.setLspRunning(running));
    }

    context.subscriptions.push(
        vscode.languages.registerHoverProvider(
            { scheme: 'file', language: 'simple' },
            hoverProvider
        )
    );
    // Also support untitled documents
    context.subscriptions.push(
        vscode.languages.registerHoverProvider(
            { scheme: 'untitled', language: 'simple' },
            hoverProvider
        )
    );

    // Register toggle preview panel command
    context.subscriptions.push(
        vscode.commands.registerCommand('simple.math.togglePreview', () => {
            if (MathPreviewPanel.isVisible()) {
                MathPreviewPanel.close();
            } else {
                MathPreviewPanel.show(decorationProvider, context.extensionUri);
            }
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('simple.math.toggleSyncPanel', () => {
            if (MathSyncPanel.isVisible()) {
                MathSyncPanel.close();
            } else {
                MathSyncPanel.show(decorationProvider, context.extensionUri);
            }
        })
    );

    // Register toggle inline rendering command
    context.subscriptions.push(
        vscode.commands.registerCommand('simple.math.toggleInlineRender', () => {
            const newState = !decorationProvider.getEnabled();
            decorationProvider.setEnabled(newState);

            // Persist to settings
            vscode.workspace.getConfiguration('simple').update(
                'math.renderInline',
                newState,
                vscode.ConfigurationTarget.Global
            );

            const message = newState
                ? 'Math inline rendering enabled'
                : 'Math inline rendering disabled';
            vscode.window.showInformationMessage(message);
        })
    );

    // Auto-open preview panel if a .spl file with math blocks is already active
    const activeEditor = vscode.window.activeTextEditor;
    if (activeEditor && activeEditor.document.languageId === 'simple') {
        const blocks = decorationProvider.detectMathBlocks(activeEditor.document);
        if (blocks.length > 0) {
            MathPreviewPanel.show(decorationProvider, context.extensionUri);
        }
    }

    // Listen for configuration changes to math.enabled
    context.subscriptions.push(
        vscode.workspace.onDidChangeConfiguration((event) => {
            if (event.affectsConfiguration('simple.math.enabled')) {
                const nowEnabled = vscode.workspace.getConfiguration('simple')
                    .get<boolean>('math.enabled', true);

                if (!nowEnabled) {
                    decorationProvider.setEnabled(false);
                    MathPreviewPanel.close();
                } else {
                    const inlineState = vscode.workspace.getConfiguration('simple')
                        .get<boolean>('math.renderInline', true);
                    decorationProvider.setEnabled(inlineState);
                }
            }
        })
    );
}
