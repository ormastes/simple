/**
 * Math module barrel export and activation
 *
 * Provides math block rendering, preview, and hover features
 * for Simple language `m{ ... }` math blocks.
 *
 * The existing Simple rendering infrastructure:
 *   src/lib/math_repr.spl    - Math expression parser with to_pretty(), render_latex_raw(), to_md()
 *   src/lib/mathjax.spl      - MathJax SFFI wrapper for SVG/HTML rendering
 *   src/app/lsp/handlers/hover.spl - LSP hover handler that renders math blocks server-side
 *   src/app/lsp/             - Full LSP server with hover, completion, diagnostics, etc.
 *
 * This module provides local TypeScript equivalents (via mathConverter.ts) for
 * quick inline preview and fallback hover when the LSP is not connected.
 */

import * as vscode from 'vscode';
import { MathDecorationProvider } from './mathDecorationProvider';
import { MathPreviewPanel } from './mathPreviewPanel';
import { MathHoverProvider } from './mathHoverProvider';

export { MathDecorationProvider } from './mathDecorationProvider';
export { MathPreviewPanel } from './mathPreviewPanel';
export { MathHoverProvider } from './mathHoverProvider';
export { simpleToLatex, simpleToUnicode } from './mathConverter';

/**
 * Activate all math-related features and register providers.
 * Call this from the main extension activate() function.
 *
 * @param context - Extension context
 * @param onLspStateChanged - Optional callback that receives a function to update
 *   LSP running state. When the LSP is running, the hover provider defers to
 *   the LSP hover handler (src/app/lsp/handlers/hover.spl) which provides
 *   full math rendering.
 */
export function activateMathFeatures(
    context: vscode.ExtensionContext,
    onLspStateChanged?: (setLspRunning: (running: boolean) => void) => void,
): void {
    const config = vscode.workspace.getConfiguration('simple');

    // Check if math features are enabled
    if (!config.get<boolean>('math.enabled', true)) {
        return;
    }

    // Create the shared decoration provider
    const decorationProvider = new MathDecorationProvider();
    context.subscriptions.push(decorationProvider);

    // Set initial inline rendering state from config
    const inlineEnabled = config.get<boolean>('math.renderInline', true);
    decorationProvider.setEnabled(inlineEnabled);

    // Register hover provider (acts as fallback when LSP is not connected)
    const hoverProvider = new MathHoverProvider(decorationProvider);

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
                MathPreviewPanel.show(decorationProvider);
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
