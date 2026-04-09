"use strict";
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
exports.simpleToUnicode = exports.simpleToLatex = exports.MathHoverProvider = exports.MathPreviewPanel = exports.MathDecorationProvider = void 0;
exports.activateMathFeatures = activateMathFeatures;
const vscode = __importStar(require("vscode"));
const mathDecorationProvider_1 = require("./mathDecorationProvider");
const mathPreviewPanel_1 = require("./mathPreviewPanel");
const mathHoverProvider_1 = require("./mathHoverProvider");
var mathDecorationProvider_2 = require("./mathDecorationProvider");
Object.defineProperty(exports, "MathDecorationProvider", { enumerable: true, get: function () { return mathDecorationProvider_2.MathDecorationProvider; } });
var mathPreviewPanel_2 = require("./mathPreviewPanel");
Object.defineProperty(exports, "MathPreviewPanel", { enumerable: true, get: function () { return mathPreviewPanel_2.MathPreviewPanel; } });
var mathHoverProvider_2 = require("./mathHoverProvider");
Object.defineProperty(exports, "MathHoverProvider", { enumerable: true, get: function () { return mathHoverProvider_2.MathHoverProvider; } });
var mathConverter_1 = require("./mathConverter");
Object.defineProperty(exports, "simpleToLatex", { enumerable: true, get: function () { return mathConverter_1.simpleToLatex; } });
Object.defineProperty(exports, "simpleToUnicode", { enumerable: true, get: function () { return mathConverter_1.simpleToUnicode; } });
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
function activateMathFeatures(context, onLspStateChanged) {
    const config = vscode.workspace.getConfiguration('simple');
    // Check if math features are enabled
    if (!config.get('math.enabled', true)) {
        return;
    }
    // Create the shared decoration provider
    const decorationProvider = new mathDecorationProvider_1.MathDecorationProvider();
    context.subscriptions.push(decorationProvider);
    // Set initial inline rendering state from config
    const inlineEnabled = config.get('math.renderInline', true);
    decorationProvider.setEnabled(inlineEnabled);
    // Register hover provider (acts as fallback when LSP is not connected)
    const hoverProvider = new mathHoverProvider_1.MathHoverProvider(decorationProvider);
    // Expose LSP state setter so the extension can notify when LSP starts/stops.
    // When LSP is running, the hover handler in src/app/lsp/handlers/hover.spl
    // provides full rendering and this provider defers to it.
    if (onLspStateChanged) {
        onLspStateChanged((running) => hoverProvider.setLspRunning(running));
    }
    context.subscriptions.push(vscode.languages.registerHoverProvider({ scheme: 'file', language: 'simple' }, hoverProvider));
    // Also support untitled documents
    context.subscriptions.push(vscode.languages.registerHoverProvider({ scheme: 'untitled', language: 'simple' }, hoverProvider));
    // Register toggle preview panel command
    context.subscriptions.push(vscode.commands.registerCommand('simple.math.togglePreview', () => {
        if (mathPreviewPanel_1.MathPreviewPanel.isVisible()) {
            mathPreviewPanel_1.MathPreviewPanel.close();
        }
        else {
            mathPreviewPanel_1.MathPreviewPanel.show(decorationProvider, context.extensionUri);
        }
    }));
    // Register toggle inline rendering command
    context.subscriptions.push(vscode.commands.registerCommand('simple.math.toggleInlineRender', () => {
        const newState = !decorationProvider.getEnabled();
        decorationProvider.setEnabled(newState);
        // Persist to settings
        vscode.workspace.getConfiguration('simple').update('math.renderInline', newState, vscode.ConfigurationTarget.Global);
        const message = newState
            ? 'Math inline rendering enabled'
            : 'Math inline rendering disabled';
        vscode.window.showInformationMessage(message);
    }));
    // Auto-open preview panel if a .spl file with math blocks is already active
    const activeEditor = vscode.window.activeTextEditor;
    if (activeEditor && activeEditor.document.languageId === 'simple') {
        const blocks = decorationProvider.detectMathBlocks(activeEditor.document);
        if (blocks.length > 0) {
            mathPreviewPanel_1.MathPreviewPanel.show(decorationProvider, context.extensionUri);
        }
    }
    // Listen for configuration changes to math.enabled
    context.subscriptions.push(vscode.workspace.onDidChangeConfiguration((event) => {
        if (event.affectsConfiguration('simple.math.enabled')) {
            const nowEnabled = vscode.workspace.getConfiguration('simple')
                .get('math.enabled', true);
            if (!nowEnabled) {
                decorationProvider.setEnabled(false);
                mathPreviewPanel_1.MathPreviewPanel.close();
            }
            else {
                const inlineState = vscode.workspace.getConfiguration('simple')
                    .get('math.renderInline', true);
                decorationProvider.setEnabled(inlineState);
            }
        }
    }));
}
//# sourceMappingURL=index.js.map