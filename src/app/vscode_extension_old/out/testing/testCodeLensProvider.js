"use strict";
/**
 * Test CodeLens Provider
 *
 * Shows "▶ Run Test" / "▶ Run File" CodeLens above:
 * - `describe "...":`  - SSpec test groups
 * - `it "...":`        - Individual test examples
 * - `context "...":`   - Test context groups
 * - `""" sdoctest:`    - Inline documentation tests
 *
 * Runs tests via `bin/simple test <file>` in the integrated terminal.
 * Runs sdoctests via `bin/simple test --sdoctest <file>`.
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
exports.TestCodeLensProvider = void 0;
exports.runTestFile = runTestFile;
exports.runSdoctest = runSdoctest;
exports.runTestAtCursor = runTestAtCursor;
const vscode = __importStar(require("vscode"));
/** Regex patterns for test block detection */
const DESCRIBE_RE = /^(\s*)(describe)\s+"([^"]+)":/;
const CONTEXT_RE = /^(\s*)(context)\s+"([^"]+)":/;
const IT_RE = /^(\s*)(it)\s+"([^"]+)":/;
const SDOCTEST_RE = /^\s*"""\s*sdoctest:/;
class TestCodeLensProvider {
    constructor() {
        this.disposables = [];
        this._onDidChangeCodeLenses = new vscode.EventEmitter();
        this.onDidChangeCodeLenses = this._onDidChangeCodeLenses.event;
        // Refresh CodeLenses when document changes
        this.disposables.push(vscode.workspace.onDidChangeTextDocument(() => {
            this._onDidChangeCodeLenses.fire();
        }));
    }
    provideCodeLenses(document, _token) {
        if (document.languageId !== 'simple') {
            return [];
        }
        const lenses = [];
        const blocks = this.detectTestBlocks(document);
        for (const block of blocks) {
            const range = new vscode.Range(block.line, 0, block.line, 0);
            if (block.kind === 'sdoctest') {
                // SDoctest: Run Doctest
                lenses.push(new vscode.CodeLens(range, {
                    title: '$(play) Run Doctest',
                    command: 'simple.test.runSdoctest',
                    arguments: [document.uri],
                    tooltip: `Run sdoctest in ${document.fileName}`,
                }));
            }
            else if (block.kind === 'describe') {
                // describe: Run File + Run Test
                lenses.push(new vscode.CodeLens(range, {
                    title: '$(play) Run File',
                    command: 'simple.test.runFile',
                    arguments: [document.uri],
                    tooltip: `Run all tests in ${document.fileName}`,
                }));
            }
            else {
                // it / context: Run Test (runs the file, since no --filter exists yet)
                lenses.push(new vscode.CodeLens(range, {
                    title: '$(play) Run Test',
                    command: 'simple.test.runFile',
                    arguments: [document.uri],
                    tooltip: `Run tests in ${document.fileName}`,
                }));
            }
        }
        return lenses;
    }
    /**
     * Detect all test blocks and sdoctest markers in a document.
     */
    detectTestBlocks(document) {
        const blocks = [];
        for (let i = 0; i < document.lineCount; i++) {
            const lineText = document.lineAt(i).text;
            let match = lineText.match(DESCRIBE_RE);
            if (match) {
                blocks.push({ kind: 'describe', label: match[3], line: i });
                continue;
            }
            match = lineText.match(CONTEXT_RE);
            if (match) {
                blocks.push({ kind: 'context', label: match[3], line: i });
                continue;
            }
            match = lineText.match(IT_RE);
            if (match) {
                blocks.push({ kind: 'it', label: match[3], line: i });
                continue;
            }
            if (SDOCTEST_RE.test(lineText)) {
                blocks.push({ kind: 'sdoctest', label: 'sdoctest', line: i });
            }
        }
        return blocks;
    }
    dispose() {
        this._onDidChangeCodeLenses.dispose();
        for (const d of this.disposables) {
            d.dispose();
        }
        this.disposables = [];
    }
}
exports.TestCodeLensProvider = TestCodeLensProvider;
/**
 * Run test file in integrated terminal.
 */
function runTestFile(uri) {
    const config = vscode.workspace.getConfiguration('simple');
    const simplePath = config.get('lsp.serverPath', 'simple');
    const filePath = uri.fsPath;
    const terminal = getOrCreateTestTerminal();
    terminal.show(true);
    terminal.sendText(`${simplePath} test "${filePath}"`);
}
/**
 * Run sdoctest for a file in integrated terminal.
 */
function runSdoctest(uri) {
    const config = vscode.workspace.getConfiguration('simple');
    const simplePath = config.get('lsp.serverPath', 'simple');
    const filePath = uri.fsPath;
    const terminal = getOrCreateTestTerminal();
    terminal.show(true);
    terminal.sendText(`${simplePath} test --sdoctest "${filePath}"`);
}
/**
 * Run test for the file currently open in the active editor.
 */
function runTestAtCursor() {
    const editor = vscode.window.activeTextEditor;
    if (!editor || editor.document.languageId !== 'simple') {
        vscode.window.showWarningMessage('No Simple file is active');
        return;
    }
    runTestFile(editor.document.uri);
}
/** Reuse or create a terminal for test output */
function getOrCreateTestTerminal() {
    const name = 'Simple Tests';
    const existing = vscode.window.terminals.find(t => t.name === name);
    if (existing) {
        return existing;
    }
    return vscode.window.createTerminal(name);
}
//# sourceMappingURL=testCodeLensProvider.js.map