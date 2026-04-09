/**
 * Math Hover Provider (fallback mode)
 *
 * Provides hover information for `m{ }` math blocks in Simple source files.
 * When the user hovers over a math block, shows:
 * - The math expression formatted nicely
 * - A link to open the preview panel
 *
 * IMPORTANT: The active LSP hover path ultimately routes through
 * `src/app/cli/query_visibility.spl hover`, which now provides server-side
 * math hover with render_latex_raw() and to_pretty() from the Simple runtime.
 * This provider acts as a FALLBACK when the LSP is not connected. When the LSP
 * is running, it handles math hover natively and this provider defers to it.
 */
import * as vscode from 'vscode';
import { MathDecorationProvider } from './mathDecorationProvider';
export declare class MathHoverProvider implements vscode.HoverProvider {
    private decorationProvider;
    private lspRunning;
    constructor(decorationProvider: MathDecorationProvider);
    /**
     * Set whether the LSP client is currently running.
     * When the LSP is running, the query-backed hover path provides math block
     * rendering, so this provider defers to it.
     */
    setLspRunning(running: boolean): void;
    /**
     * Provide hover information for math blocks.
     *
     * When the LSP is running, returns null to let the query/LSP hover path
     * provide the response instead.
     * Acts as fallback when LSP is not connected.
     */
    provideHover(document: vscode.TextDocument, position: vscode.Position, _token: vscode.CancellationToken): vscode.ProviderResult<vscode.Hover>;
    /**
     * Create a hover display for a math block (fallback mode).
     *
     * Uses local TypeScript converters from mathConverter.ts which mirror
     * the Simple-side rendering in src/lib/math_repr.spl.
     */
    private createHover;
}
