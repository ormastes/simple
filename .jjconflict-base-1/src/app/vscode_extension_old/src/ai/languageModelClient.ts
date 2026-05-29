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

export class LanguageModelClient {
    private models: vscode.LanguageModelChat[] = [];
    private selectedModelId: string | null = null;

    constructor(private outputChannel: vscode.OutputChannel) {}

    /**
     * Initialize language model access and discover available models
     */
    async initialize(): Promise<void> {
        try {
            // Get all available language models
            this.models = await vscode.lm.selectChatModels({
                vendor: 'copilot',
                family: 'gpt-4'
            });

            if (this.models.length === 0) {
                // Fallback to any available model
                this.models = await vscode.lm.selectChatModels();
            }

            if (this.models.length > 0) {
                this.selectedModelId = this.models[0].id;
                this.log(`Initialized with ${this.models.length} language model(s)`);
                this.log(`Selected model: ${this.selectedModelId}`);
            } else {
                this.log('WARNING: No language models available', 'error');
            }
        } catch (error) {
            this.log(`Error initializing language models: ${error}`, 'error');
        }
    }

    /**
     * Check if language models are available
     */
    isAvailable(): boolean {
        return this.models.length > 0;
    }

    /**
     * Get list of available models
     */
    getAvailableModels(): string[] {
        return this.models.map(m => `${m.vendor}/${m.family} (${m.id})`);
    }

    /**
     * Send a chat request to the language model
     */
    async chat(
        messages: ChatMessage[],
        options?: ChatOptions,
        cancellationToken?: vscode.CancellationToken
    ): Promise<string> {
        if (!this.isAvailable()) {
            throw new Error('No language models available. Please install GitHub Copilot or another compatible extension.');
        }

        try {
            const model = this.models[0];

            // Convert our message format to VSCode format
            const vscodeMessages = messages.map(msg => {
                if (msg.role === 'user') {
                    return vscode.LanguageModelChatMessage.User(msg.content);
                } else if (msg.role === 'assistant') {
                    return vscode.LanguageModelChatMessage.Assistant(msg.content);
                } else {
                    return vscode.LanguageModelChatMessage.User(msg.content);
                }
            });

            // Prepare request options
            const requestOptions: vscode.LanguageModelChatRequestOptions = {};
            if (options?.maxTokens) {
                // VSCode API doesn't expose maxTokens directly yet
                // This may be added in future versions
            }

            this.log(`Sending chat request with ${messages.length} messages`);

            // Send request
            const response = await model.sendRequest(
                vscodeMessages,
                requestOptions,
                cancellationToken || new vscode.CancellationTokenSource().token
            );

            // Collect response text
            let result = '';
            for await (const fragment of response.text) {
                result += fragment;
            }

            this.log(`Received response: ${result.substring(0, 100)}...`);
            return result;

        } catch (error: any) {
            if (error.message?.includes('model not found')) {
                throw new Error('Language model not available. Please ensure GitHub Copilot is installed and activated.');
            }
            throw error;
        }
    }

    /**
     * Generate code completion suggestion
     */
    async complete(
        context: CompletionContext,
        cancellationToken?: vscode.CancellationToken
    ): Promise<string> {
        const prompt = this.buildCompletionPrompt(context);

        const messages: ChatMessage[] = [
            {
                role: 'system',
                content: 'You are a code completion assistant for the Simple programming language. Provide only the completion code without explanations.'
            },
            {
                role: 'user',
                content: prompt
            }
        ];

        return await this.chat(messages, { maxTokens: 200 }, cancellationToken);
    }

    /**
     * Explain code snippet
     */
    async explain(code: string, language: string = 'simple'): Promise<string> {
        const messages: ChatMessage[] = [
            {
                role: 'system',
                content: 'You are an expert in the Simple programming language. Explain code clearly and concisely.'
            },
            {
                role: 'user',
                content: `Explain this ${language} code:\n\n\`\`\`${language}\n${code}\n\`\`\``
            }
        ];

        return await this.chat(messages);
    }

    /**
     * Review code and suggest improvements
     */
    async review(code: string, language: string = 'simple'): Promise<string> {
        const messages: ChatMessage[] = [
            {
                role: 'system',
                content: 'You are a code reviewer for the Simple programming language. Focus on correctness, performance, and best practices.'
            },
            {
                role: 'user',
                content: `Review this ${language} code and suggest improvements:\n\n\`\`\`${language}\n${code}\n\`\`\``
            }
        ];

        return await this.chat(messages);
    }

    /**
     * Generate code from natural language description
     */
    async generate(description: string, language: string = 'simple'): Promise<string> {
        const messages: ChatMessage[] = [
            {
                role: 'system',
                content: 'You are a code generator for the Simple programming language. Generate clean, idiomatic code based on descriptions.'
            },
            {
                role: 'user',
                content: `Generate ${language} code for: ${description}`
            }
        ];

        return await this.chat(messages);
    }

    /**
     * Build completion prompt from context
     */
    private buildCompletionPrompt(context: CompletionContext): string {
        const lines = context.code.split('\n');
        const currentLine = context.position.line;
        const currentCol = context.position.character;

        // Get context before and after cursor
        const before = lines.slice(Math.max(0, currentLine - 10), currentLine + 1).join('\n');
        const after = lines.slice(currentLine + 1, Math.min(lines.length, currentLine + 5)).join('\n');

        let prompt = `Complete the following ${context.language} code:\n\n`;

        if (context.fileContext) {
            prompt += `File context:\n${context.fileContext}\n\n`;
        }

        prompt += '```' + context.language + '\n';
        prompt += before;
        prompt += '<CURSOR>';
        if (after) {
            prompt += '\n' + after;
        }
        prompt += '\n```\n\n';
        prompt += 'Provide only the code that should be inserted at <CURSOR>, without any explanations or markdown.';

        return prompt;
    }

    /**
     * Log message to output channel
     */
    private log(message: string, level: 'info' | 'error' = 'info'): void {
        const timestamp = new Date().toISOString();
        const prefix = level === 'error' ? '[ERROR]' : '[INFO]';
        this.outputChannel.appendLine(`${timestamp} ${prefix} ${message}`);
    }
}
