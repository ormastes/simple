"use strict";
/**
 * Test Utilities - Helper functions for VSCode extension testing
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
exports.SAMPLE_CODE = exports.TestUtils = void 0;
const vscode = __importStar(require("vscode"));
const path = __importStar(require("path"));
const fs = __importStar(require("fs"));
class TestUtils {
    /**
     * Create a temporary .spl file with content
     */
    static async createTestFile(filename, content) {
        const workspaceFolder = vscode.workspace.workspaceFolders?.[0];
        if (!workspaceFolder) {
            throw new Error('No workspace folder found');
        }
        const filePath = path.join(workspaceFolder.uri.fsPath, filename);
        // Create file
        fs.writeFileSync(filePath, content, 'utf-8');
        // Open in VSCode
        const uri = vscode.Uri.file(filePath);
        const doc = await vscode.workspace.openTextDocument(uri);
        await vscode.window.showTextDocument(doc);
        return doc;
    }
    /**
     * Delete a test file
     */
    static deleteTestFile(filename) {
        const workspaceFolder = vscode.workspace.workspaceFolders?.[0];
        if (!workspaceFolder) {
            return;
        }
        const filePath = path.join(workspaceFolder.uri.fsPath, filename);
        if (fs.existsSync(filePath)) {
            fs.unlinkSync(filePath);
        }
    }
    /**
     * Wait for condition to be true
     */
    static async waitFor(condition, timeout = 5000, interval = 100) {
        const startTime = Date.now();
        while (Date.now() - startTime < timeout) {
            if (await condition()) {
                return;
            }
            await this.sleep(interval);
        }
        throw new Error(`Timeout waiting for condition after ${timeout}ms`);
    }
    /**
     * Sleep for specified milliseconds
     */
    static sleep(ms) {
        return new Promise(resolve => setTimeout(resolve, ms));
    }
    /**
     * Wait for LSP to be ready
     */
    static async waitForLSP(timeout = 10000) {
        await this.waitFor(() => {
            const extension = vscode.extensions.getExtension('simple-lang.simple-language');
            return extension?.isActive ?? false;
        }, timeout);
        // Additional wait for LSP server to fully start
        await this.sleep(2000);
    }
    /**
     * Get all diagnostics for a document
     */
    static async getDiagnostics(uri) {
        // Wait a bit for diagnostics to be published
        await this.sleep(500);
        return vscode.languages.getDiagnostics(uri);
    }
    /**
     * Trigger completion at position
     */
    static async triggerCompletion(document, position) {
        const result = await vscode.commands.executeCommand('vscode.executeCompletionItemProvider', document.uri, position);
        return result;
    }
    /**
     * Get hover information at position
     */
    static async getHover(document, position) {
        const result = await vscode.commands.executeCommand('vscode.executeHoverProvider', document.uri, position);
        return result || [];
    }
    /**
     * Go to definition at position
     */
    static async goToDefinition(document, position) {
        const result = await vscode.commands.executeCommand('vscode.executeDefinitionProvider', document.uri, position);
        return result || [];
    }
    /**
     * Find all references at position
     */
    static async findReferences(document, position) {
        const result = await vscode.commands.executeCommand('vscode.executeReferenceProvider', document.uri, position);
        return result || [];
    }
    /**
     * Get semantic tokens for document
     */
    static async getSemanticTokens(document) {
        const result = await vscode.commands.executeCommand('vscode.provideDocumentSemanticTokens', document.uri);
        return result;
    }
    /**
     * Type text at current position
     */
    static async typeText(text) {
        await vscode.commands.executeCommand('type', { text });
    }
    /**
     * Execute command and wait for completion
     */
    static async executeCommand(command, ...args) {
        return await vscode.commands.executeCommand(command, ...args);
    }
    /**
     * Get active text editor
     */
    static getActiveEditor() {
        return vscode.window.activeTextEditor;
    }
    /**
     * Set cursor position
     */
    static async setCursorPosition(editor, line, character) {
        const position = new vscode.Position(line, character);
        editor.selection = new vscode.Selection(position, position);
        editor.revealRange(new vscode.Range(position, position));
    }
    /**
     * Select text range
     */
    static async selectRange(editor, startLine, startChar, endLine, endChar) {
        const start = new vscode.Position(startLine, startChar);
        const end = new vscode.Position(endLine, endChar);
        editor.selection = new vscode.Selection(start, end);
        editor.revealRange(new vscode.Range(start, end));
    }
    /**
     * Insert text at position
     */
    static async insertText(editor, position, text) {
        return await editor.edit(editBuilder => {
            editBuilder.insert(position, text);
        });
    }
    /**
     * Replace text in range
     */
    static async replaceText(editor, range, text) {
        return await editor.edit(editBuilder => {
            editBuilder.replace(range, text);
        });
    }
    /**
     * Close all editors
     */
    static async closeAllEditors() {
        await vscode.commands.executeCommand('workbench.action.closeAllEditors');
    }
    /**
     * Get extension
     */
    static getExtension() {
        return vscode.extensions.getExtension('simple-lang.simple-language');
    }
    /**
     * Check if extension is active
     */
    static isExtensionActive() {
        const extension = this.getExtension();
        return extension?.isActive ?? false;
    }
    /**
     * Activate extension
     */
    static async activateExtension() {
        const extension = this.getExtension();
        if (!extension) {
            throw new Error('Extension not found');
        }
        if (!extension.isActive) {
            await extension.activate();
        }
    }
    /**
     * Get configuration value
     */
    static getConfig(section, key) {
        return vscode.workspace.getConfiguration(section).get(key);
    }
    /**
     * Update configuration value
     */
    static async updateConfig(section, key, value, target = vscode.ConfigurationTarget.Workspace) {
        await vscode.workspace.getConfiguration(section).update(key, value, target);
    }
}
exports.TestUtils = TestUtils;
/**
 * Sample Simple code snippets for testing
 */
exports.SAMPLE_CODE = {
    simple_function: `fn add(x: i32, y: i32): i32 = x + y

fn main():
    let result = add(10, 20)
    print(result)
`,
    class_definition: `class Point:
    x: i32
    y: i32

    fn new(x: i32, y: i32): Point =
        Point(x: x, y: y)

    fn distance(self): f64 =
        sqrt(self.x * self.x + self.y * self.y)
`,
    with_errors: `fn broken(x: i32
    let y = x +
    return
`,
    async_function: `async fn fetch_data(url: String): Result<String, String> =
    let response = await http.get(url)
    Ok(response.body)

fn main():
    let data = await fetch_data("https://api.example.com")
    print(data)
`,
    imports: `import std.io
import std.collections as coll
from std.math import sqrt, pow

fn main():
    io.println("Hello, World!")
`,
    fibonacci: `fn fibonacci(n: i32): i32 =
    if n <= 1:
        n
    else:
        fibonacci(n - 1) + fibonacci(n - 2)
`
};
//# sourceMappingURL=testUtils.js.map