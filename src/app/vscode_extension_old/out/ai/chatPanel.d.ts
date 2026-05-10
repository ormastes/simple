/**
 * AI Chat Panel - Interactive chat interface using webview
 * Provides a side panel for conversing with the language model
 */
import * as vscode from 'vscode';
import { LanguageModelClient } from './languageModelClient';
export declare class ChatPanel {
    static currentPanel: ChatPanel | undefined;
    private readonly panel;
    private readonly lmClient;
    private readonly extensionUri;
    private chatHistory;
    private disposables;
    private constructor();
    /**
     * Show or create the chat panel
     */
    static show(extensionUri: vscode.Uri, lmClient: LanguageModelClient): void;
    /**
     * Handle messages from webview
     */
    private handleMessage;
    /**
     * Handle chat message from user
     */
    private handleChatMessage;
    /**
     * Explain currently selected code
     */
    private handleExplainSelection;
    /**
     * Review currently selected code
     */
    private handleReviewSelection;
    /**
     * Send message to webview
     */
    private sendMessage;
    /**
     * Get HTML content for webview
     */
    private getHtmlContent;
    /**
     * Dispose of resources
     */
    dispose(): void;
}
