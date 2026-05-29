/**
 * AI Inline Completion Provider
 * Provides AI-powered code completions as the user types (ghost text)
 */

import * as vscode from 'vscode';
import { LanguageModelClient, CompletionContext } from './languageModelClient';

export class AIInlineCompletionProvider implements vscode.InlineCompletionItemProvider {
    private lmClient: LanguageModelClient;
    private enabled: boolean = true;
    private lastRequest: number = 0;
    private debounceMs: number = 300;
    private minCharsForCompletion: number = 10;

    constructor(lmClient: LanguageModelClient) {
        this.lmClient = lmClient;
    }

    /**
     * Enable or disable inline completions
     */
    setEnabled(enabled: boolean) {
        this.enabled = enabled;
    }

    /**
     * Check if inline completions are enabled
     */
    isEnabled(): boolean {
        return this.enabled;
    }

    /**
     * Provide inline completion items
     */
    async provideInlineCompletionItems(
        document: vscode.TextDocument,
        position: vscode.Position,
        context: vscode.InlineCompletionContext,
        token: vscode.CancellationToken
    ): Promise<vscode.InlineCompletionItem[] | vscode.InlineCompletionList | undefined> {
        // Skip if disabled or model not available
        if (!this.enabled || !this.lmClient.isAvailable()) {
            return undefined;
        }

        // Skip if only language is not Simple
        if (document.languageId !== 'simple') {
            return undefined;
        }

        // Debounce - avoid too frequent requests
        const now = Date.now();
        if (now - this.lastRequest < this.debounceMs) {
            return undefined;
        }
        this.lastRequest = now;

        // Skip if cursor is not at end of line or if line is too short
        const line = document.lineAt(position.line);
        const isAtEndOfLine = position.character === line.text.length;
        const lineText = line.text.trim();

        if (!isAtEndOfLine || lineText.length < this.minCharsForCompletion) {
            return undefined;
        }

        // Skip if triggered by specific characters (let LSP handle those)
        const triggerChar = document.getText(new vscode.Range(
            position.translate(0, -1),
            position
        ));

        if (['.', '(', '[', '{', ','].includes(triggerChar)) {
            return undefined;
        }

        try {
            // Build completion context
            const completionContext: CompletionContext = {
                code: document.getText(),
                position: position,
                language: document.languageId,
                fileContext: this.getFileContext(document)
            };

            // Get AI completion
            const completion = await this.lmClient.complete(completionContext, token);

            if (!completion || completion.trim().length === 0) {
                return undefined;
            }

            // Clean up completion (remove markdown, extra whitespace, etc.)
            const cleanedCompletion = this.cleanCompletion(completion);

            if (!cleanedCompletion) {
                return undefined;
            }

            // Create inline completion item
            const item = new vscode.InlineCompletionItem(
                cleanedCompletion,
                new vscode.Range(position, position)
            );

            // Set command to be executed when completion is accepted
            item.command = {
                command: 'simple.ai.completionAccepted',
                title: 'AI Completion Accepted'
            };

            return [item];

        } catch (error) {
            // Silent fail - don't show errors for inline completions
            console.error('Inline completion error:', error);
            return undefined;
        }
    }

    /**
     * Get relevant file context (imports, surrounding functions, etc.)
     */
    private getFileContext(document: vscode.TextDocument): string {
        const text = document.getText();
        const lines = text.split('\n');

        // Extract imports (first ~20 lines typically)
        const imports = lines
            .slice(0, Math.min(20, lines.length))
            .filter(line => line.trim().startsWith('import') || line.trim().startsWith('from'))
            .join('\n');

        // Extract class/function signatures
        const signatures = lines
            .filter(line => {
                const trimmed = line.trim();
                return trimmed.startsWith('fn ') ||
                       trimmed.startsWith('class ') ||
                       trimmed.startsWith('trait ') ||
                       trimmed.startsWith('enum ');
            })
            .join('\n');

        return `${imports}\n\n${signatures}`.trim();
    }

    /**
     * Clean up AI completion text
     */
    private cleanCompletion(completion: string): string {
        let cleaned = completion;

        // Remove markdown code blocks
        cleaned = cleaned.replace(/```[\w]*\n/g, '');
        cleaned = cleaned.replace(/```/g, '');

        // Remove explanatory text (lines starting with #, //, or containing "explanation")
        const lines = cleaned.split('\n');
        const codeLines = lines.filter(line => {
            const trimmed = line.trim();
            return !trimmed.startsWith('#') &&
                   !trimmed.startsWith('//') &&
                   !trimmed.toLowerCase().includes('explanation') &&
                   !trimmed.toLowerCase().includes('here is') &&
                   !trimmed.toLowerCase().includes('this code');
        });

        cleaned = codeLines.join('\n');

        // Trim whitespace
        cleaned = cleaned.trim();

        // If completion is too long (>5 lines), truncate
        const finalLines = cleaned.split('\n');
        if (finalLines.length > 5) {
            cleaned = finalLines.slice(0, 5).join('\n');
        }

        return cleaned;
    }
}
