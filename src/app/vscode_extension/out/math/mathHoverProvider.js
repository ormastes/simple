"use strict";
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
exports.MathHoverProvider = void 0;
const vscode = __importStar(require("vscode"));
const mathConverter_1 = require("./mathConverter");
class MathHoverProvider {
    constructor(decorationProvider) {
        this.decorationProvider = decorationProvider;
        this.lspRunning = false;
    }
    /**
     * Set whether the LSP client is currently running.
     * When the LSP is running, the query-backed hover path provides math block
     * rendering, so this provider defers to it.
     */
    setLspRunning(running) {
        this.lspRunning = running;
    }
    /**
     * Provide hover information for math blocks.
     *
     * When the LSP is running, returns null to let the query/LSP hover path
     * provide the response instead.
     * Acts as fallback when LSP is not connected.
     */
    provideHover(document, position, _token) {
        // When LSP is running, defer to the query/LSP hover path which
        // provides full rendering via render_latex_raw() and to_pretty().
        if (this.lspRunning) {
            return null;
        }
        const config = vscode.workspace.getConfiguration('simple');
        if (!config.get('math.previewOnHover', true)) {
            return null;
        }
        const mathBlocks = this.decorationProvider.detectMathBlocks(document);
        for (const block of mathBlocks) {
            if (block.fullRange.contains(position)) {
                return this.createHover(block.content, block.fullRange);
            }
        }
        return null;
    }
    /**
     * Create a hover display for a math block (fallback mode).
     *
     * Uses local TypeScript converters from mathConverter.ts which mirror
     * the Simple-side rendering in src/lib/math_repr.spl.
     */
    createHover(content, range) {
        const markdown = new vscode.MarkdownString();
        markdown.isTrusted = true;
        markdown.supportHtml = true;
        // Header
        markdown.appendMarkdown('**Math Block** `m{ }`\n\n');
        markdown.appendMarkdown('---\n\n');
        // Display math via VSCode's built-in KaTeX rendering
        const latex = (0, mathConverter_1.simpleToLatex)(content);
        markdown.appendMarkdown(`$$${latex}$$\n\n`);
        // Separator
        markdown.appendMarkdown('---\n\n');
        // Unicode pretty text (mirrors to_pretty() from src/lib/math_repr.spl)
        const pretty = (0, mathConverter_1.simpleToUnicode)(content);
        markdown.appendMarkdown(`**Pretty:** ${pretty}\n\n`);
        // Source
        markdown.appendMarkdown(`**Source:** \`${content}\`\n\n`);
        // Action link to open preview panel
        const openPreviewCommand = vscode.Uri.parse(`command:simple.math.togglePreview`);
        markdown.appendMarkdown(`[Open Math Preview Panel](${openPreviewCommand})`);
        return new vscode.Hover(markdown, range);
    }
}
exports.MathHoverProvider = MathHoverProvider;
//# sourceMappingURL=mathHoverProvider.js.map