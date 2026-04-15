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
export { MathCustomEditorProvider } from './mathCustomEditor';
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
export declare function activateMathFeatures(context: vscode.ExtensionContext, onLspStateChanged?: (setLspRunning: (running: boolean) => void) => void, debugLogger?: (message: string) => void): void;
