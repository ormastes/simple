# VSCode Language Model Protocol (LMP) Integration Plan

**Date:** 2025-12-26
**Goal:** Add AI-powered features to VSCode extension via Language Model Protocol

## Executive Summary

Extend the Simple VSCode extension with Language Model Protocol (LMP) support, enabling:

- 🤖 **AI Chat** - Interactive coding assistant
- ✨ **Smart Completions** - Context-aware code suggestions
- 📝 **Code Generation** - Generate code from natural language
- 🔍 **Code Explanation** - Explain complex code
- ✅ **Code Review** - AI-powered code analysis
- 🔧 **Refactoring Suggestions** - Intelligent code improvements

**Approach:** Integrate with VSCode's Language Model API (Copilot API) and custom LMP server

---

## Architecture Overview

### High-Level Flow

```
User Request (Chat/Completion/Explain)
       │
       ▼
VSCode Extension (TypeScript)
       │
       ├─> VSCode Language Model API (Copilot)
       │   └─> GPT-4, Claude, etc.
       │
       └─> Custom LMP Server (Simple)
           └─> Local models, custom logic
       │
       ▼
AI Response → Format → Display in VSCode
```

### Components

**1. VSCode Extension (TypeScript)**
- Chat panel UI
- Inline completion provider
- Code action provider (AI-powered)
- Webview for AI chat interface

**2. LMP Handlers (Simple)**
- Chat completion handler
- Code completion handler
- Code explanation handler
- Code review handler

**3. Model Integrations**
- VSCode built-in models (via Copilot API)
- OpenAI API (optional)
- Anthropic Claude API (optional)
- Local models (llama.cpp, ollama)

---

## Implementation Plan

### Phase 1: VSCode Language Model API Integration (Day 1, ~400 LOC)

**Goal:** Use VSCode's built-in Language Model API for chat and completions

**Files to Create:**

**1. `vscode-extension/src/ai/languageModelClient.ts`** (~150 lines)

```typescript
import * as vscode from 'vscode';

export class LanguageModelClient {
    private models: vscode.LanguageModelChat[] = [];

    async initialize() {
        // Get available language models (Copilot, etc.)
        this.models = await vscode.lm.selectChatModels({
            family: 'gpt-4'  // or 'claude', 'gemini'
        });
    }

    async chat(prompt: string, context?: string): Promise<string> {
        if (this.models.length === 0) {
            throw new Error('No language models available');
        }

        const messages = [
            vscode.LanguageModelChatMessage.User(prompt)
        ];

        if (context) {
            messages.unshift(
                vscode.LanguageModelChatMessage.User(
                    `Context:\n${context}\n\nQuestion:`
                )
            );
        }

        const response = await this.models[0].sendRequest(
            messages,
            {},
            new vscode.CancellationTokenSource().token
        );

        let result = '';
        for await (const chunk of response.text) {
            result += chunk;
        }

        return result;
    }

    async complete(code: string, cursor: vscode.Position): Promise<string> {
        const prompt = `Complete the following Simple code:\n\n${code}\n\nContinue from cursor position line ${cursor.line}, column ${cursor.character}:`;

        return this.chat(prompt);
    }

    async explain(code: string): Promise<string> {
        const prompt = `Explain this Simple code:\n\n\`\`\`simple\n${code}\n\`\`\`\n\nProvide a clear explanation of what this code does.`;

        return this.chat(prompt);
    }

    async review(code: string): Promise<string> {
        const prompt = `Review this Simple code for potential issues:\n\n\`\`\`simple\n${code}\n\`\`\`\n\nProvide suggestions for:\n- Code quality\n- Performance\n- Security\n- Best practices`;

        return this.chat(prompt);
    }

    async generateCode(description: string): Promise<string> {
        const prompt = `Generate Simple code for: ${description}\n\nProvide only the code, no explanations.`;

        return this.chat(prompt);
    }
}
```

**2. `vscode-extension/src/ai/chatPanel.ts`** (~200 lines)

```typescript
import * as vscode from 'vscode';
import { LanguageModelClient } from './languageModelClient';

export class ChatPanel {
    private panel: vscode.WebviewPanel | undefined;
    private lmClient: LanguageModelClient;

    constructor(context: vscode.ExtensionContext, lmClient: LanguageModelClient) {
        this.lmClient = lmClient;
    }

    async show() {
        if (this.panel) {
            this.panel.reveal();
            return;
        }

        this.panel = vscode.window.createWebviewPanel(
            'simpleChatPanel',
            'Simple AI Assistant',
            vscode.ViewColumn.Beside,
            {
                enableScripts: true,
                retainContextWhenHidden: true
            }
        );

        this.panel.webview.html = this.getWebviewContent();

        this.panel.webview.onDidReceiveMessage(async (message) => {
            switch (message.command) {
                case 'chat':
                    await this.handleChat(message.text);
                    break;
                case 'explain':
                    await this.handleExplain();
                    break;
                case 'review':
                    await this.handleReview();
                    break;
            }
        });

        this.panel.onDidDispose(() => {
            this.panel = undefined;
        });
    }

    private async handleChat(text: string) {
        const editor = vscode.window.activeTextEditor;
        const context = editor ? editor.document.getText() : undefined;

        this.panel?.webview.postMessage({
            type: 'thinking'
        });

        try {
            const response = await this.lmClient.chat(text, context);

            this.panel?.webview.postMessage({
                type: 'response',
                text: response
            });
        } catch (error) {
            this.panel?.webview.postMessage({
                type: 'error',
                text: `Error: ${error}`
            });
        }
    }

    private getWebviewContent(): string {
        return `<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Simple AI Assistant</title>
    <style>
        body {
            font-family: var(--vscode-font-family);
            padding: 10px;
            color: var(--vscode-foreground);
            background: var(--vscode-editor-background);
        }
        #chat-container {
            display: flex;
            flex-direction: column;
            height: 100vh;
        }
        #messages {
            flex: 1;
            overflow-y: auto;
            margin-bottom: 10px;
        }
        .message {
            margin: 10px 0;
            padding: 10px;
            border-radius: 5px;
        }
        .user {
            background: var(--vscode-input-background);
        }
        .assistant {
            background: var(--vscode-editor-inactiveSelectionBackground);
        }
        #input-container {
            display: flex;
            gap: 10px;
        }
        #input {
            flex: 1;
            padding: 8px;
            background: var(--vscode-input-background);
            color: var(--vscode-input-foreground);
            border: 1px solid var(--vscode-input-border);
        }
        button {
            padding: 8px 16px;
            background: var(--vscode-button-background);
            color: var(--vscode-button-foreground);
            border: none;
            cursor: pointer;
        }
        button:hover {
            background: var(--vscode-button-hoverBackground);
        }
    </style>
</head>
<body>
    <div id="chat-container">
        <div id="messages"></div>
        <div id="input-container">
            <input type="text" id="input" placeholder="Ask me anything about Simple...">
            <button onclick="send()">Send</button>
        </div>
    </div>
    <script>
        const vscode = acquireVsCodeApi();

        function send() {
            const input = document.getElementById('input');
            const text = input.value.trim();
            if (!text) return;

            addMessage('user', text);
            input.value = '';

            vscode.postMessage({ command: 'chat', text: text });
        }

        function addMessage(role, text) {
            const messages = document.getElementById('messages');
            const div = document.createElement('div');
            div.className = 'message ' + role;
            div.textContent = text;
            messages.appendChild(div);
            messages.scrollTop = messages.scrollHeight;
        }

        window.addEventListener('message', event => {
            const message = event.data;
            switch (message.type) {
                case 'thinking':
                    addMessage('assistant', 'Thinking...');
                    break;
                case 'response':
                    const messages = document.getElementById('messages');
                    const thinking = messages.querySelector('.assistant:last-child');
                    if (thinking && thinking.textContent === 'Thinking...') {
                        messages.removeChild(thinking);
                    }
                    addMessage('assistant', message.text);
                    break;
                case 'error':
                    addMessage('assistant', message.text);
                    break;
            }
        });

        document.getElementById('input').addEventListener('keypress', (e) => {
            if (e.key === 'Enter') send();
        });
    </script>
</body>
</html>`;
    }
}
```

**3. `vscode-extension/src/ai/inlineCompletionProvider.ts`** (~50 lines)

```typescript
import * as vscode from 'vscode';
import { LanguageModelClient } from './languageModelClient';

export class AIInlineCompletionProvider implements vscode.InlineCompletionItemProvider {
    constructor(private lmClient: LanguageModelClient) {}

    async provideInlineCompletionItems(
        document: vscode.TextDocument,
        position: vscode.Position,
        context: vscode.InlineCompletionContext,
        token: vscode.CancellationToken
    ): Promise<vscode.InlineCompletionItem[]> {

        const code = document.getText();
        const completion = await this.lmClient.complete(code, position);

        if (!completion) {
            return [];
        }

        return [
            new vscode.InlineCompletionItem(
                completion,
                new vscode.Range(position, position)
            )
        ];
    }
}
```

---

### Phase 2: Custom LMP Server (Day 2, ~500 LOC)

**Goal:** Simple-based LMP server for custom AI logic

**Files to Create:**

**1. `simple/app/lmp/main.spl`** (~100 lines)

```simple
# Language Model Protocol Server
# Provides AI-powered code assistance

import sys
import lmp.server as server
import lmp.transport as transport

fn main():
    print("Starting Simple LMP Server...")

    # Initialize server
    let srv = server.LmpServer.new()

    # Start message loop
    transport.run_message_loop(srv)

    print("LMP Server stopped")
```

**2. `simple/app/lmp/server.spl`** (~200 lines)

```simple
# LMP Server Implementation

import lmp.protocol as protocol
import lmp.handlers.{chat, completion, explanation, review}

enum ServerState:
    Uninitialized
    Initialized
    ShuttingDown

class LmpServer:
    state: ServerState
    model_provider: String  # "openai", "anthropic", "local"
    api_key: Option[String]

    fn new() -> LmpServer:
        LmpServer(
            state: ServerState.Uninitialized,
            model_provider: "local",
            api_key: none
        )

    fn handle_initialize(self, id: i64, params: Option[Dict]) -> Result[Nil, String]:
        # Extract configuration
        if params != none:
            let config = params!

            if config.has_key("modelProvider"):
                self.model_provider = config["modelProvider"]

            if config.has_key("apiKey"):
                self.api_key = some(config["apiKey"])

        self.state = ServerState.Initialized

        # Send initialize response
        let result = {
            "capabilities": {
                "chat": true,
                "completion": true,
                "explanation": true,
                "review": true,
                "codeGeneration": true
            }
        }

        transport.write_response(id, result)?
        Ok(nil)

    fn handle_chat(self, id: i64, params: Dict) -> Result[Nil, String]:
        let prompt = params["prompt"].as_string()
        let context = if params.has_key("context"):
            some(params["context"].as_string())
        else:
            none

        # Call chat handler
        let response = chat.handle_chat_request(
            prompt,
            context,
            self.model_provider,
            self.api_key
        )?

        transport.write_response(id, {"text": response})?
        Ok(nil)

    fn handle_completion(self, id: i64, params: Dict) -> Result[Nil, String]:
        let code = params["code"].as_string()
        let cursor_line = params["line"].as_i32()
        let cursor_col = params["column"].as_i32()

        let response = completion.handle_completion_request(
            code,
            cursor_line,
            cursor_col,
            self.model_provider,
            self.api_key
        )?

        transport.write_response(id, {"completion": response})?
        Ok(nil)

    fn handle_explain(self, id: i64, params: Dict) -> Result[Nil, String]:
        let code = params["code"].as_string()

        let response = explanation.handle_explain_request(
            code,
            self.model_provider,
            self.api_key
        )?

        transport.write_response(id, {"explanation": response})?
        Ok(nil)

    fn handle_review(self, id: i64, params: Dict) -> Result[Nil, String]:
        let code = params["code"].as_string()

        let response = review.handle_review_request(
            code,
            self.model_provider,
            self.api_key
        )?

        transport.write_response(id, {"review": response})?
        Ok(nil)
```

**3. `simple/app/lmp/handlers/chat.spl`** (~100 lines)

```simple
# Chat Handler
# Handles conversational AI requests

fn handle_chat_request(
    prompt: String,
    context: Option[String],
    provider: String,
    api_key: Option[String]
) -> Result[String, String]:

    # Build full prompt with context
    let full_prompt = if context != none:
        f"Context:\n{context!}\n\nQuestion: {prompt}"
    else:
        prompt

    # Route to appropriate provider
    match provider:
        case "openai":
            call_openai(full_prompt, api_key)
        case "anthropic":
            call_anthropic(full_prompt, api_key)
        case "local":
            call_local_model(full_prompt)
        case _:
            Err(f"Unknown provider: {provider}")

fn call_local_model(prompt: String) -> Result[String, String]:
    # Placeholder for local model integration
    # TODO: Integrate with llama.cpp or ollama

    Ok("Local model response (placeholder)")

fn call_openai(prompt: String, api_key: Option[String]) -> Result[String, String]:
    if api_key == none:
        return Err("OpenAI API key required")

    # TODO: Implement OpenAI API call
    Ok("OpenAI response (placeholder)")

fn call_anthropic(prompt: String, api_key: Option[String]) -> Result[String, String]:
    if api_key == none:
        return Err("Anthropic API key required")

    # TODO: Implement Claude API call
    Ok("Claude response (placeholder)")
```

---

### Phase 3: AI-Powered Code Actions (Day 3, ~300 LOC)

**Goal:** Integrate AI into VSCode code actions

**Files to Update:**

**1. `vscode-extension/src/extension.ts`** (add AI features)

```typescript
import { LanguageModelClient } from './ai/languageModelClient';
import { ChatPanel } from './ai/chatPanel';
import { AIInlineCompletionProvider } from './ai/inlineCompletionProvider';

export async function activate(context: vscode.ExtensionContext) {
    // ... existing LSP client setup ...

    // Initialize Language Model client
    const lmClient = new LanguageModelClient();
    await lmClient.initialize();

    // Register chat panel
    const chatPanel = new ChatPanel(context, lmClient);

    context.subscriptions.push(
        vscode.commands.registerCommand('simple.ai.openChat', () => {
            chatPanel.show();
        })
    );

    // Register inline completion provider
    context.subscriptions.push(
        vscode.languages.registerInlineCompletionItemProvider(
            { language: 'simple' },
            new AIInlineCompletionProvider(lmClient)
        )
    );

    // Register AI commands
    context.subscriptions.push(
        vscode.commands.registerCommand('simple.ai.explainCode', async () => {
            const editor = vscode.window.activeTextEditor;
            if (!editor) return;

            const selection = editor.selection;
            const code = editor.document.getText(selection);

            const explanation = await lmClient.explain(code);

            vscode.window.showInformationMessage(explanation, {
                modal: true
            });
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('simple.ai.reviewCode', async () => {
            const editor = vscode.window.activeTextEditor;
            if (!editor) return;

            const code = editor.document.getText();
            const review = await lmClient.review(code);

            // Show in output channel
            const outputChannel = vscode.window.createOutputChannel('Simple AI Review');
            outputChannel.clear();
            outputChannel.appendLine(review);
            outputChannel.show();
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('simple.ai.generateCode', async () => {
            const description = await vscode.window.showInputBox({
                prompt: 'Describe the code you want to generate',
                placeHolder: 'e.g., "A function to calculate factorial"'
            });

            if (!description) return;

            const code = await lmClient.generateCode(description);

            const editor = vscode.window.activeTextEditor;
            if (editor) {
                editor.edit(editBuilder => {
                    editBuilder.insert(editor.selection.active, code);
                });
            }
        })
    );
}
```

**2. Update `package.json`** (add AI commands)

```json
{
  "contributes": {
    "commands": [
      {
        "command": "simple.ai.openChat",
        "title": "Open AI Chat",
        "category": "Simple AI"
      },
      {
        "command": "simple.ai.explainCode",
        "title": "Explain Selected Code",
        "category": "Simple AI"
      },
      {
        "command": "simple.ai.reviewCode",
        "title": "Review Current File",
        "category": "Simple AI"
      },
      {
        "command": "simple.ai.generateCode",
        "title": "Generate Code",
        "category": "Simple AI"
      }
    ],
    "menus": {
      "editor/context": [
        {
          "when": "editorLangId == simple",
          "command": "simple.ai.explainCode",
          "group": "simple@1"
        }
      ]
    },
    "configuration": {
      "properties": {
        "simple.ai.provider": {
          "type": "string",
          "enum": ["vscode", "openai", "anthropic", "local"],
          "default": "vscode",
          "description": "AI model provider"
        },
        "simple.ai.apiKey": {
          "type": "string",
          "default": "",
          "description": "API key for external AI provider"
        },
        "simple.ai.enableInlineCompletions": {
          "type": "boolean",
          "default": true,
          "description": "Enable AI-powered inline completions"
        }
      }
    }
  }
}
```

---

## Feature Summary

### AI Chat Panel
- Interactive chat with AI about Simple code
- Context-aware (includes current file)
- Persistent chat history

### Inline Completions
- AI-powered code suggestions as you type
- Ghost text completions (like Copilot)
- Triggered automatically or manually (Ctrl+Space)

### Code Explanation
- Select code → Right-click → "Explain Selected Code"
- Get natural language explanation

### Code Review
- Command Palette → "Simple AI: Review Current File"
- Get suggestions for improvements

### Code Generation
- Command Palette → "Simple AI: Generate Code"
- Describe what you want → AI generates code

---

## Success Criteria

✅ **Chat works** - Users can chat with AI about code
✅ **Completions work** - Inline suggestions appear as you type
✅ **Explanations work** - Selected code gets explained
✅ **Review works** - Files get AI-powered review
✅ **Generation works** - Natural language → code

---

## Timeline

| Phase | Days | LOC | Deliverable |
|-------|------|-----|-------------|
| 1. VSCode LM API | 1 | 400 | Chat, completions, commands |
| 2. Custom LMP Server | 1 | 500 | Simple-based AI server |
| 3. Code Actions | 1 | 300 | Context menu integration |
| **Total** | **3** | **1,200** | **Full AI integration** |

---

## Next Steps

1. Implement Phase 1 (VSCode Language Model API)
2. Test chat panel and inline completions
3. Implement Phase 2 (Custom LMP server)
4. Add Phase 3 (Code actions)
5. Create comprehensive docs

---

**Plan Status:** Ready for implementation
**Dependencies:** VSCode 1.90+ (for Language Model API)
**Effort:** ~1,200 lines over 3 days
