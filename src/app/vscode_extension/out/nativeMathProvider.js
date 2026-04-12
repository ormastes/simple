"use strict";
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
exports.NativeMathProvider = void 0;
const vscode = __importStar(require("vscode"));
const blockDetector_1 = require("./blockDetector");
const mathPreview_1 = require("./mathPreview");
function makeRange(document, from, to) {
    return new vscode.Range(document.positionAt(from), document.positionAt(to));
}
function asDecorationBlock(document, block) {
    if (!(0, mathPreview_1.isMathLikeBlock)(block.kind)) {
        return undefined;
    }
    const fullRange = makeRange(document, block.from, block.to);
    const openRange = makeRange(document, block.from, block.prefixEnd);
    const contentRange = makeRange(document, block.prefixEnd, block.to - 1);
    const closeRange = makeRange(document, block.to - 1, block.to);
    return { block, fullRange, openRange, contentRange, closeRange };
}
function rangesOverlap(a, b) {
    return !(a.end.isBeforeOrEqual(b.start) || b.end.isBeforeOrEqual(a.start));
}
function diagnosticDecorationForRange(diagnostics, range) {
    let severity;
    for (const diagnostic of diagnostics) {
        if (!rangesOverlap(diagnostic.range, range)) {
            continue;
        }
        if (severity === undefined || diagnostic.severity < severity) {
            severity = diagnostic.severity;
        }
    }
    if (severity === vscode.DiagnosticSeverity.Error) {
        return 'text-decoration: underline wavy var(--vscode-editorError-foreground);';
    }
    if (severity === vscode.DiagnosticSeverity.Warning) {
        return 'text-decoration: underline wavy var(--vscode-editorWarning-foreground);';
    }
    if (severity === vscode.DiagnosticSeverity.Information) {
        return 'text-decoration: underline dotted var(--vscode-editorInfo-foreground);';
    }
    if (severity === vscode.DiagnosticSeverity.Hint) {
        return 'text-decoration: underline dotted var(--vscode-editorHint-foreground);';
    }
    return undefined;
}
function hasBlockingDiagnostic(diagnostics, range) {
    return diagnostics.some((diagnostic) => rangesOverlap(diagnostic.range, range)
        && (diagnostic.severity === vscode.DiagnosticSeverity.Error
            || diagnostic.severity === vscode.DiagnosticSeverity.Warning));
}
function selectionIntersectsBlock(document, selections, block) {
    for (const selection of selections) {
        const selectionStart = document.offsetAt(selection.start);
        const selectionEnd = document.offsetAt(selection.end);
        if (selection.isEmpty) {
            if (selectionStart >= block.from && selectionStart <= block.to) {
                return true;
            }
            continue;
        }
        if (selectionStart < block.to && selectionEnd > block.from) {
            return true;
        }
    }
    return false;
}
function buildMathHoverMarkdown(block, preview) {
    if (!preview) {
        return undefined;
    }
    const markdown = new vscode.MarkdownString(undefined, true);
    markdown.appendMarkdown(`**${preview.label}**\n\n`);
    markdown.appendCodeblock(block.content, 'simple');
    markdown.appendMarkdown('\n');
    markdown.appendMarkdown(`Preview: \`${preview.displayText}\``);
    return markdown;
}
class NativeMathProvider {
    constructor() {
        this.lspRunning = false;
        this.openDecoration = vscode.window.createTextEditorDecorationType({
            opacity: '0',
        });
        this.closeDecoration = vscode.window.createTextEditorDecorationType({
            opacity: '0',
        });
        this.contentDecoration = vscode.window.createTextEditorDecorationType({
            opacity: '0',
        });
        this.previewDecoration = vscode.window.createTextEditorDecorationType({});
        this.disposables = [];
        this.disposables.push(vscode.window.onDidChangeActiveTextEditor((editor) => {
            if (editor) {
                this.refreshEditor(editor);
            }
        }), vscode.window.onDidChangeTextEditorSelection((event) => {
            this.refreshEditor(event.textEditor);
        }), vscode.workspace.onDidChangeTextDocument((event) => {
            for (const editor of vscode.window.visibleTextEditors) {
                if (editor.document.uri.toString() === event.document.uri.toString()) {
                    this.refreshEditor(editor);
                }
            }
        }), vscode.workspace.onDidChangeConfiguration((event) => {
            if (event.affectsConfiguration('simple.math.enabled') ||
                event.affectsConfiguration('simple.math.renderInline')) {
                this.refreshVisibleEditors();
            }
        }));
        this.refreshVisibleEditors();
    }
    provideHover(document, position) {
        if (this.lspRunning) {
            return undefined;
        }
        const config = vscode.workspace.getConfiguration('simple.math');
        if (!config.get('enabled', true) || !config.get('previewOnHover', true)) {
            return undefined;
        }
        const block = this.findMathBlockAtPosition(document, position);
        if (!block) {
            return undefined;
        }
        const preview = (0, mathPreview_1.buildMathPreview)(block);
        if (!preview) {
            return undefined;
        }
        const activeEditor = vscode.window.activeTextEditor;
        if (activeEditor?.document.uri.toString() !== document.uri.toString()) {
            return undefined;
        }
        if (!selectionIntersectsBlock(document, activeEditor.selections, block)) {
            return undefined;
        }
        const markdown = buildMathHoverMarkdown(block, preview);
        if (!markdown) {
            return undefined;
        }
        return new vscode.Hover(markdown, makeRange(document, block.from, block.to));
    }
    setLspRunning(running) {
        this.lspRunning = running;
    }
    findMathBlockAtPosition(document, position) {
        const offset = document.offsetAt(position);
        return (0, blockDetector_1.detectBlocks)(document.getText()).find((block) => (0, mathPreview_1.isMathLikeBlock)(block.kind) && offset >= block.from && offset <= block.to);
    }
    dispose() {
        this.openDecoration.dispose();
        this.closeDecoration.dispose();
        this.contentDecoration.dispose();
        this.previewDecoration.dispose();
        for (const disposable of this.disposables) {
            disposable.dispose();
        }
    }
    refreshVisibleEditors() {
        for (const editor of vscode.window.visibleTextEditors) {
            this.refreshEditor(editor);
        }
    }
    refreshEditor(editor) {
        if (editor.document.languageId !== 'simple') {
            return;
        }
        const config = vscode.workspace.getConfiguration('simple.math');
        if (!config.get('enabled', true) || !config.get('renderInline', true)) {
            editor.setDecorations(this.openDecoration, []);
            editor.setDecorations(this.closeDecoration, []);
            editor.setDecorations(this.contentDecoration, []);
            editor.setDecorations(this.previewDecoration, []);
            return;
        }
        const openDecorations = [];
        const closeDecorations = [];
        const contentDecorations = [];
        const diagnostics = vscode.languages.getDiagnostics(editor.document.uri);
        for (const block of (0, blockDetector_1.detectBlocks)(editor.document.getText())) {
            const decoration = asDecorationBlock(editor.document, block);
            const preview = (0, mathPreview_1.buildMathPreview)(block);
            if (!decoration || !preview) {
                continue;
            }
            if (hasBlockingDiagnostic(diagnostics, decoration.fullRange)) {
                continue;
            }
            if (selectionIntersectsBlock(editor.document, editor.selections, block)) {
                continue;
            }
            openDecorations.push({
                range: decoration.openRange,
                hoverMessage: buildMathHoverMarkdown(block, preview),
                renderOptions: {
                    before: {
                        contentText: preview.displayText,
                        color: new vscode.ThemeColor('editorLineNumber.foreground'),
                        margin: '0 0.25rem 0 0',
                        textDecoration: diagnosticDecorationForRange(diagnostics, decoration.fullRange),
                    },
                },
            });
            closeDecorations.push(decoration.closeRange);
            contentDecorations.push(decoration.contentRange);
        }
        editor.setDecorations(this.openDecoration, openDecorations);
        editor.setDecorations(this.closeDecoration, closeDecorations);
        editor.setDecorations(this.contentDecoration, contentDecorations);
        editor.setDecorations(this.previewDecoration, []);
    }
}
exports.NativeMathProvider = NativeMathProvider;
//# sourceMappingURL=nativeMathProvider.js.map