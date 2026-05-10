/**
 * Test Utilities - Helper functions for VSCode extension testing
 */
import * as vscode from 'vscode';
export declare class TestUtils {
    /**
     * Create a temporary .spl file with content
     */
    static createTestFile(filename: string, content: string): Promise<vscode.TextDocument>;
    /**
     * Delete a test file
     */
    static deleteTestFile(filename: string): void;
    /**
     * Wait for condition to be true
     */
    static waitFor(condition: () => boolean | Promise<boolean>, timeout?: number, interval?: number): Promise<void>;
    /**
     * Sleep for specified milliseconds
     */
    static sleep(ms: number): Promise<void>;
    /**
     * Wait for LSP to be ready
     */
    static waitForLSP(timeout?: number): Promise<void>;
    /**
     * Get all diagnostics for a document
     */
    static getDiagnostics(uri: vscode.Uri): Promise<vscode.Diagnostic[]>;
    /**
     * Trigger completion at position
     */
    static triggerCompletion(document: vscode.TextDocument, position: vscode.Position): Promise<vscode.CompletionList | undefined>;
    /**
     * Get hover information at position
     */
    static getHover(document: vscode.TextDocument, position: vscode.Position): Promise<vscode.Hover[]>;
    /**
     * Go to definition at position
     */
    static goToDefinition(document: vscode.TextDocument, position: vscode.Position): Promise<vscode.Location[]>;
    /**
     * Find all references at position
     */
    static findReferences(document: vscode.TextDocument, position: vscode.Position): Promise<vscode.Location[]>;
    /**
     * Get semantic tokens for document
     */
    static getSemanticTokens(document: vscode.TextDocument): Promise<vscode.SemanticTokens | undefined>;
    /**
     * Type text at current position
     */
    static typeText(text: string): Promise<void>;
    /**
     * Execute command and wait for completion
     */
    static executeCommand<T>(command: string, ...args: any[]): Promise<T | undefined>;
    /**
     * Get active text editor
     */
    static getActiveEditor(): vscode.TextEditor | undefined;
    /**
     * Set cursor position
     */
    static setCursorPosition(editor: vscode.TextEditor, line: number, character: number): Promise<void>;
    /**
     * Select text range
     */
    static selectRange(editor: vscode.TextEditor, startLine: number, startChar: number, endLine: number, endChar: number): Promise<void>;
    /**
     * Insert text at position
     */
    static insertText(editor: vscode.TextEditor, position: vscode.Position, text: string): Promise<boolean>;
    /**
     * Replace text in range
     */
    static replaceText(editor: vscode.TextEditor, range: vscode.Range, text: string): Promise<boolean>;
    /**
     * Close all editors
     */
    static closeAllEditors(): Promise<void>;
    /**
     * Get extension
     */
    static getExtension(): vscode.Extension<any> | undefined;
    /**
     * Check if extension is active
     */
    static isExtensionActive(): boolean;
    /**
     * Activate extension
     */
    static activateExtension(): Promise<void>;
    /**
     * Get configuration value
     */
    static getConfig<T>(section: string, key: string): T | undefined;
    /**
     * Update configuration value
     */
    static updateConfig(section: string, key: string, value: any, target?: vscode.ConfigurationTarget): Promise<void>;
}
/**
 * Sample Simple code snippets for testing
 */
export declare const SAMPLE_CODE: {
    simple_function: string;
    class_definition: string;
    with_errors: string;
    async_function: string;
    imports: string;
    fibonacci: string;
};
