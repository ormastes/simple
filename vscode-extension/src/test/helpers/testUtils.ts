/**
 * Test Utilities - Helper functions for VSCode extension testing
 */

import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';

export class TestUtils {
    /**
     * Create a temporary .spl file with content
     */
    static async createTestFile(
        filename: string,
        content: string
    ): Promise<vscode.TextDocument> {
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
    static deleteTestFile(filename: string): void {
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
    static async waitFor(
        condition: () => boolean | Promise<boolean>,
        timeout: number = 5000,
        interval: number = 100
    ): Promise<void> {
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
    static sleep(ms: number): Promise<void> {
        return new Promise(resolve => setTimeout(resolve, ms));
    }

    /**
     * Wait for LSP to be ready
     */
    static async waitForLSP(timeout: number = 10000): Promise<void> {
        await this.waitFor(
            () => {
                const extension = vscode.extensions.getExtension('simple-lang.simple-language');
                return extension?.isActive ?? false;
            },
            timeout
        );

        // Additional wait for LSP server to fully start
        await this.sleep(2000);
    }

    /**
     * Get all diagnostics for a document
     */
    static async getDiagnostics(uri: vscode.Uri): Promise<vscode.Diagnostic[]> {
        // Wait a bit for diagnostics to be published
        await this.sleep(500);
        return vscode.languages.getDiagnostics(uri);
    }

    /**
     * Trigger completion at position
     */
    static async triggerCompletion(
        document: vscode.TextDocument,
        position: vscode.Position
    ): Promise<vscode.CompletionList | undefined> {
        const result = await vscode.commands.executeCommand<vscode.CompletionList>(
            'vscode.executeCompletionItemProvider',
            document.uri,
            position
        );
        return result;
    }

    /**
     * Get hover information at position
     */
    static async getHover(
        document: vscode.TextDocument,
        position: vscode.Position
    ): Promise<vscode.Hover[]> {
        const result = await vscode.commands.executeCommand<vscode.Hover[]>(
            'vscode.executeHoverProvider',
            document.uri,
            position
        );
        return result || [];
    }

    /**
     * Go to definition at position
     */
    static async goToDefinition(
        document: vscode.TextDocument,
        position: vscode.Position
    ): Promise<vscode.Location[]> {
        const result = await vscode.commands.executeCommand<vscode.Location[]>(
            'vscode.executeDefinitionProvider',
            document.uri,
            position
        );
        return result || [];
    }

    /**
     * Find all references at position
     */
    static async findReferences(
        document: vscode.TextDocument,
        position: vscode.Position
    ): Promise<vscode.Location[]> {
        const result = await vscode.commands.executeCommand<vscode.Location[]>(
            'vscode.executeReferenceProvider',
            document.uri,
            position
        );
        return result || [];
    }

    /**
     * Get semantic tokens for document
     */
    static async getSemanticTokens(
        document: vscode.TextDocument
    ): Promise<vscode.SemanticTokens | undefined> {
        const result = await vscode.commands.executeCommand<vscode.SemanticTokens>(
            'vscode.provideDocumentSemanticTokens',
            document.uri
        );
        return result;
    }

    /**
     * Type text at current position
     */
    static async typeText(text: string): Promise<void> {
        await vscode.commands.executeCommand('type', { text });
    }

    /**
     * Execute command and wait for completion
     */
    static async executeCommand<T>(
        command: string,
        ...args: any[]
    ): Promise<T | undefined> {
        return await vscode.commands.executeCommand<T>(command, ...args);
    }

    /**
     * Get active text editor
     */
    static getActiveEditor(): vscode.TextEditor | undefined {
        return vscode.window.activeTextEditor;
    }

    /**
     * Set cursor position
     */
    static async setCursorPosition(
        editor: vscode.TextEditor,
        line: number,
        character: number
    ): Promise<void> {
        const position = new vscode.Position(line, character);
        editor.selection = new vscode.Selection(position, position);
        editor.revealRange(new vscode.Range(position, position));
    }

    /**
     * Select text range
     */
    static async selectRange(
        editor: vscode.TextEditor,
        startLine: number,
        startChar: number,
        endLine: number,
        endChar: number
    ): Promise<void> {
        const start = new vscode.Position(startLine, startChar);
        const end = new vscode.Position(endLine, endChar);
        editor.selection = new vscode.Selection(start, end);
        editor.revealRange(new vscode.Range(start, end));
    }

    /**
     * Insert text at position
     */
    static async insertText(
        editor: vscode.TextEditor,
        position: vscode.Position,
        text: string
    ): Promise<boolean> {
        return await editor.edit(editBuilder => {
            editBuilder.insert(position, text);
        });
    }

    /**
     * Replace text in range
     */
    static async replaceText(
        editor: vscode.TextEditor,
        range: vscode.Range,
        text: string
    ): Promise<boolean> {
        return await editor.edit(editBuilder => {
            editBuilder.replace(range, text);
        });
    }

    /**
     * Close all editors
     */
    static async closeAllEditors(): Promise<void> {
        await vscode.commands.executeCommand('workbench.action.closeAllEditors');
    }

    /**
     * Get extension
     */
    static getExtension(): vscode.Extension<any> | undefined {
        return vscode.extensions.getExtension('simple-lang.simple-language');
    }

    /**
     * Check if extension is active
     */
    static isExtensionActive(): boolean {
        const extension = this.getExtension();
        return extension?.isActive ?? false;
    }

    /**
     * Activate extension
     */
    static async activateExtension(): Promise<void> {
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
    static getConfig<T>(section: string, key: string): T | undefined {
        return vscode.workspace.getConfiguration(section).get<T>(key);
    }

    /**
     * Update configuration value
     */
    static async updateConfig(
        section: string,
        key: string,
        value: any,
        target: vscode.ConfigurationTarget = vscode.ConfigurationTarget.Workspace
    ): Promise<void> {
        await vscode.workspace.getConfiguration(section).update(key, value, target);
    }
}

/**
 * Sample Simple code snippets for testing
 */
export const SAMPLE_CODE = {
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
