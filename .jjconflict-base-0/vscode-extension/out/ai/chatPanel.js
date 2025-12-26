"use strict";
/**
 * AI Chat Panel - Interactive chat interface using webview
 * Provides a side panel for conversing with the language model
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
exports.ChatPanel = void 0;
const vscode = __importStar(require("vscode"));
class ChatPanel {
    constructor(panel, extensionUri, lmClient) {
        this.chatHistory = [];
        this.disposables = [];
        this.panel = panel;
        this.extensionUri = extensionUri;
        this.lmClient = lmClient;
        // Set initial HTML content
        this.panel.webview.html = this.getHtmlContent();
        // Handle messages from webview
        this.panel.webview.onDidReceiveMessage(message => this.handleMessage(message), null, this.disposables);
        // Clean up on close
        this.panel.onDidDispose(() => this.dispose(), null, this.disposables);
    }
    /**
     * Show or create the chat panel
     */
    static show(extensionUri, lmClient) {
        const column = vscode.window.activeTextEditor
            ? vscode.window.activeTextEditor.viewColumn
            : undefined;
        // If we already have a panel, show it
        if (ChatPanel.currentPanel) {
            ChatPanel.currentPanel.panel.reveal(column);
            return;
        }
        // Create new panel
        const panel = vscode.window.createWebviewPanel('simpleChatPanel', 'Simple AI Assistant', column || vscode.ViewColumn.Beside, {
            enableScripts: true,
            retainContextWhenHidden: true,
            localResourceRoots: [extensionUri]
        });
        ChatPanel.currentPanel = new ChatPanel(panel, extensionUri, lmClient);
    }
    /**
     * Handle messages from webview
     */
    async handleMessage(message) {
        switch (message.type) {
            case 'chat':
                await this.handleChatMessage(message.text);
                break;
            case 'clear':
                this.chatHistory = [];
                this.sendMessage({ type: 'cleared' });
                break;
            case 'explainSelection':
                await this.handleExplainSelection();
                break;
            case 'reviewSelection':
                await this.handleReviewSelection();
                break;
            case 'ready':
                // Webview is ready, send initial state
                this.sendMessage({
                    type: 'init',
                    modelsAvailable: this.lmClient.isAvailable(),
                    models: this.lmClient.getAvailableModels()
                });
                break;
        }
    }
    /**
     * Handle chat message from user
     */
    async handleChatMessage(text) {
        if (!text.trim()) {
            return;
        }
        // Add user message to history
        const userMessage = { role: 'user', content: text };
        this.chatHistory.push(userMessage);
        // Show user message in UI
        this.sendMessage({
            type: 'userMessage',
            text: text
        });
        // Show thinking indicator
        this.sendMessage({ type: 'thinking', value: true });
        try {
            // Get AI response
            const response = await this.lmClient.chat(this.chatHistory);
            // Add assistant message to history
            const assistantMessage = { role: 'assistant', content: response };
            this.chatHistory.push(assistantMessage);
            // Show assistant message in UI
            this.sendMessage({
                type: 'assistantMessage',
                text: response
            });
        }
        catch (error) {
            this.sendMessage({
                type: 'error',
                text: error.message || 'An error occurred while communicating with the language model.'
            });
        }
        finally {
            this.sendMessage({ type: 'thinking', value: false });
        }
    }
    /**
     * Explain currently selected code
     */
    async handleExplainSelection() {
        const editor = vscode.window.activeTextEditor;
        if (!editor) {
            this.sendMessage({ type: 'error', text: 'No active editor' });
            return;
        }
        const selection = editor.selection;
        const code = editor.document.getText(selection);
        if (!code.trim()) {
            this.sendMessage({ type: 'error', text: 'No code selected' });
            return;
        }
        this.sendMessage({ type: 'thinking', value: true });
        try {
            const explanation = await this.lmClient.explain(code, editor.document.languageId);
            this.sendMessage({
                type: 'assistantMessage',
                text: `**Explanation of selected code:**\n\n${explanation}`
            });
        }
        catch (error) {
            this.sendMessage({ type: 'error', text: error.message });
        }
        finally {
            this.sendMessage({ type: 'thinking', value: false });
        }
    }
    /**
     * Review currently selected code
     */
    async handleReviewSelection() {
        const editor = vscode.window.activeTextEditor;
        if (!editor) {
            this.sendMessage({ type: 'error', text: 'No active editor' });
            return;
        }
        const selection = editor.selection;
        const code = editor.document.getText(selection);
        if (!code.trim()) {
            this.sendMessage({ type: 'error', text: 'No code selected' });
            return;
        }
        this.sendMessage({ type: 'thinking', value: true });
        try {
            const review = await this.lmClient.review(code, editor.document.languageId);
            this.sendMessage({
                type: 'assistantMessage',
                text: `**Code Review:**\n\n${review}`
            });
        }
        catch (error) {
            this.sendMessage({ type: 'error', text: error.message });
        }
        finally {
            this.sendMessage({ type: 'thinking', value: false });
        }
    }
    /**
     * Send message to webview
     */
    sendMessage(message) {
        this.panel.webview.postMessage(message);
    }
    /**
     * Get HTML content for webview
     */
    getHtmlContent() {
        return `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Simple AI Assistant</title>
    <style>
        body {
            font-family: var(--vscode-font-family);
            font-size: var(--vscode-font-size);
            color: var(--vscode-foreground);
            background-color: var(--vscode-editor-background);
            margin: 0;
            padding: 0;
            display: flex;
            flex-direction: column;
            height: 100vh;
        }

        #header {
            padding: 12px 16px;
            background-color: var(--vscode-sideBar-background);
            border-bottom: 1px solid var(--vscode-panel-border);
            display: flex;
            justify-content: space-between;
            align-items: center;
        }

        #header h2 {
            margin: 0;
            font-size: 14px;
            font-weight: 600;
        }

        #clearBtn {
            background: var(--vscode-button-background);
            color: var(--vscode-button-foreground);
            border: none;
            padding: 4px 12px;
            border-radius: 2px;
            cursor: pointer;
            font-size: 12px;
        }

        #clearBtn:hover {
            background: var(--vscode-button-hoverBackground);
        }

        #chatContainer {
            flex: 1;
            overflow-y: auto;
            padding: 16px;
        }

        .message {
            margin-bottom: 16px;
            padding: 12px;
            border-radius: 4px;
        }

        .message.user {
            background-color: var(--vscode-input-background);
            border-left: 3px solid var(--vscode-textLink-foreground);
        }

        .message.assistant {
            background-color: var(--vscode-editor-inactiveSelectionBackground);
            border-left: 3px solid var(--vscode-notificationsInfoIcon-foreground);
        }

        .message.error {
            background-color: var(--vscode-inputValidation-errorBackground);
            border-left: 3px solid var(--vscode-inputValidation-errorBorder);
            color: var(--vscode-errorForeground);
        }

        .message pre {
            background-color: var(--vscode-textBlockQuote-background);
            padding: 8px;
            border-radius: 3px;
            overflow-x: auto;
        }

        .message code {
            font-family: var(--vscode-editor-font-family);
            font-size: var(--vscode-editor-font-size);
        }

        #thinking {
            display: none;
            padding: 12px;
            text-align: center;
            color: var(--vscode-descriptionForeground);
            font-style: italic;
        }

        #thinking.visible {
            display: block;
        }

        #inputContainer {
            padding: 16px;
            background-color: var(--vscode-sideBar-background);
            border-top: 1px solid var(--vscode-panel-border);
        }

        #inputBox {
            width: 100%;
            padding: 8px;
            background-color: var(--vscode-input-background);
            color: var(--vscode-input-foreground);
            border: 1px solid var(--vscode-input-border);
            border-radius: 2px;
            font-family: inherit;
            font-size: inherit;
            resize: vertical;
            min-height: 60px;
        }

        #inputBox:focus {
            outline: 1px solid var(--vscode-focusBorder);
        }

        #actionButtons {
            margin-top: 8px;
            display: flex;
            gap: 8px;
        }

        .actionBtn {
            background: var(--vscode-button-background);
            color: var(--vscode-button-foreground);
            border: none;
            padding: 6px 12px;
            border-radius: 2px;
            cursor: pointer;
            font-size: 12px;
        }

        .actionBtn:hover {
            background: var(--vscode-button-hoverBackground);
        }

        .actionBtn.secondary {
            background: var(--vscode-button-secondaryBackground);
            color: var(--vscode-button-secondaryForeground);
        }

        .actionBtn.secondary:hover {
            background: var(--vscode-button-secondaryHoverBackground);
        }
    </style>
</head>
<body>
    <div id="header">
        <h2>Simple AI Assistant</h2>
        <button id="clearBtn">Clear Chat</button>
    </div>

    <div id="chatContainer"></div>

    <div id="thinking">Thinking...</div>

    <div id="inputContainer">
        <textarea id="inputBox" placeholder="Ask me anything about Simple code..."></textarea>
        <div id="actionButtons">
            <button class="actionBtn" id="sendBtn">Send</button>
            <button class="actionBtn secondary" id="explainBtn">Explain Selection</button>
            <button class="actionBtn secondary" id="reviewBtn">Review Selection</button>
        </div>
    </div>

    <script>
        const vscode = acquireVsCodeApi();
        const chatContainer = document.getElementById('chatContainer');
        const inputBox = document.getElementById('inputBox');
        const sendBtn = document.getElementById('sendBtn');
        const clearBtn = document.getElementById('clearBtn');
        const explainBtn = document.getElementById('explainBtn');
        const reviewBtn = document.getElementById('reviewBtn');
        const thinkingIndicator = document.getElementById('thinking');

        // Handle messages from extension
        window.addEventListener('message', event => {
            const message = event.data;

            switch (message.type) {
                case 'init':
                    if (!message.modelsAvailable) {
                        addMessage('error', 'No language models available. Please install GitHub Copilot or another compatible extension.');
                    }
                    break;

                case 'userMessage':
                    addMessage('user', message.text);
                    break;

                case 'assistantMessage':
                    addMessage('assistant', message.text);
                    break;

                case 'error':
                    addMessage('error', message.text);
                    break;

                case 'thinking':
                    thinkingIndicator.classList.toggle('visible', message.value);
                    break;

                case 'cleared':
                    chatContainer.innerHTML = '';
                    break;
            }
        });

        // Send chat message
        function sendMessage() {
            const text = inputBox.value.trim();
            if (text) {
                vscode.postMessage({ type: 'chat', text: text });
                inputBox.value = '';
            }
        }

        // Add message to chat
        function addMessage(type, text) {
            const messageDiv = document.createElement('div');
            messageDiv.className = 'message ' + type;

            // Simple markdown rendering
            let html = text
                .replace(/\`([^\`]+)\`/g, '<code>$1</code>')
                .replace(/\\*\\*([^*]+)\\*\\*/g, '<strong>$1</strong>')
                .replace(/\\n/g, '<br>');

            // Handle code blocks
            html = html.replace(/\`\`\`(\\w+)?\\n([\\s\\S]*?)\`\`\`/g, '<pre><code>$2</code></pre>');

            messageDiv.innerHTML = html;
            chatContainer.appendChild(messageDiv);
            chatContainer.scrollTop = chatContainer.scrollHeight;
        }

        // Event listeners
        sendBtn.addEventListener('click', sendMessage);
        clearBtn.addEventListener('click', () => vscode.postMessage({ type: 'clear' }));
        explainBtn.addEventListener('click', () => vscode.postMessage({ type: 'explainSelection' }));
        reviewBtn.addEventListener('click', () => vscode.postMessage({ type: 'reviewSelection' }));

        inputBox.addEventListener('keydown', (e) => {
            if (e.key === 'Enter' && e.ctrlKey) {
                sendMessage();
            }
        });

        // Notify extension that webview is ready
        vscode.postMessage({ type: 'ready' });
    </script>
</body>
</html>`;
    }
    /**
     * Dispose of resources
     */
    dispose() {
        ChatPanel.currentPanel = undefined;
        this.panel.dispose();
        while (this.disposables.length) {
            const disposable = this.disposables.pop();
            if (disposable) {
                disposable.dispose();
            }
        }
    }
}
exports.ChatPanel = ChatPanel;
//# sourceMappingURL=chatPanel.js.map