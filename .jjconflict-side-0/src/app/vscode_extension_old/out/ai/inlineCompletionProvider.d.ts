/**
 * AI Inline Completion Provider
 * Provides AI-powered code completions as the user types (ghost text)
 */
import * as vscode from 'vscode';
import { LanguageModelClient } from './languageModelClient';
export declare class AIInlineCompletionProvider implements vscode.InlineCompletionItemProvider {
    private lmClient;
    private enabled;
    private lastRequest;
    private debounceMs;
    private minCharsForCompletion;
    constructor(lmClient: LanguageModelClient);
    /**
     * Enable or disable inline completions
     */
    setEnabled(enabled: boolean): void;
    /**
     * Check if inline completions are enabled
     */
    isEnabled(): boolean;
    /**
     * Provide inline completion items
     */
    provideInlineCompletionItems(document: vscode.TextDocument, position: vscode.Position, context: vscode.InlineCompletionContext, token: vscode.CancellationToken): Promise<vscode.InlineCompletionItem[] | vscode.InlineCompletionList | undefined>;
    /**
     * Get relevant file context (imports, surrounding functions, etc.)
     */
    private getFileContext;
    /**
     * Clean up AI completion text
     */
    private cleanCompletion;
}
