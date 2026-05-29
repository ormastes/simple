/**
 * Language Model Client - VSCode Language Model API Integration
 * Provides access to VSCode's built-in language models (Copilot, etc.)
 */
import * as vscode from 'vscode';
export interface ChatMessage {
    role: 'user' | 'assistant' | 'system';
    content: string;
}
export interface ChatOptions {
    maxTokens?: number;
    temperature?: number;
    topP?: number;
    stopSequences?: string[];
}
export interface CompletionContext {
    code: string;
    position: vscode.Position;
    language: string;
    fileContext?: string;
}
export declare class LanguageModelClient {
    private outputChannel;
    private models;
    private selectedModelId;
    constructor(outputChannel: vscode.OutputChannel);
    /**
     * Initialize language model access and discover available models
     */
    initialize(): Promise<void>;
    /**
     * Check if language models are available
     */
    isAvailable(): boolean;
    /**
     * Get list of available models
     */
    getAvailableModels(): string[];
    /**
     * Send a chat request to the language model
     */
    chat(messages: ChatMessage[], options?: ChatOptions, cancellationToken?: vscode.CancellationToken): Promise<string>;
    /**
     * Generate code completion suggestion
     */
    complete(context: CompletionContext, cancellationToken?: vscode.CancellationToken): Promise<string>;
    /**
     * Explain code snippet
     */
    explain(code: string, language?: string): Promise<string>;
    /**
     * Review code and suggest improvements
     */
    review(code: string, language?: string): Promise<string>;
    /**
     * Generate code from natural language description
     */
    generate(description: string, language?: string): Promise<string>;
    /**
     * Build completion prompt from context
     */
    private buildCompletionPrompt;
    /**
     * Log message to output channel
     */
    private log;
}
