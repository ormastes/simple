/**
 * Simple UI Panel - Webview panel for Simple UI widgets
 *
 * Shows a webview panel that renders Simple UI widget trees.
 * The Simple process generates HTML via the VscodeBackend,
 * and this panel displays it with bidirectional event communication.
 *
 * Modeled on mathPreviewPanel.ts.
 */

import * as vscode from 'vscode';

export class SimpleUiPanel implements vscode.Disposable {
    public static currentPanel: SimpleUiPanel | undefined;

    private readonly panel: vscode.WebviewPanel;
    private disposables: vscode.Disposable[] = [];

    /** Currently displayed HTML content (to avoid redundant updates) */
    private currentHtml: string | null = null;

    /** Callback for events from the webview */
    private onEvent: ((type: string, payload: string) => void) | null = null;

    private constructor(panel: vscode.WebviewPanel) {
        this.panel = panel;

        // Set initial HTML
        this.panel.webview.html = this.getWrapperHtml('', 'dark');

        // Handle messages from the webview
        this.disposables.push(
            this.panel.webview.onDidReceiveMessage((message) => {
                this.handleWebviewMessage(message);
            })
        );

        // Clean up on close
        this.panel.onDidDispose(() => this.dispose(), null, this.disposables);
    }

    /**
     * Show or create the Simple UI panel.
     */
    public static show(title?: string): SimpleUiPanel {
        const column = vscode.window.activeTextEditor
            ? vscode.window.activeTextEditor.viewColumn
            : undefined;

        // If we already have a panel, reveal it
        if (SimpleUiPanel.currentPanel) {
            SimpleUiPanel.currentPanel.panel.reveal(
                column ? column + 1 : vscode.ViewColumn.Beside
            );
            return SimpleUiPanel.currentPanel;
        }

        // Create new panel
        const panel = vscode.window.createWebviewPanel(
            'simpleUi',
            title || 'Simple UI',
            {
                viewColumn: vscode.ViewColumn.Beside,
                preserveFocus: true,
            },
            {
                enableScripts: true,
                retainContextWhenHidden: true,
            }
        );

        SimpleUiPanel.currentPanel = new SimpleUiPanel(panel);
        return SimpleUiPanel.currentPanel;
    }

    /**
     * Check if the panel is currently visible.
     */
    public static isVisible(): boolean {
        return SimpleUiPanel.currentPanel !== undefined;
    }

    /**
     * Close the panel if open.
     */
    public static close(): void {
        if (SimpleUiPanel.currentPanel) {
            SimpleUiPanel.currentPanel.panel.dispose();
        }
    }

    /**
     * Set the event handler for webview messages.
     */
    public setEventHandler(handler: (type: string, payload: string) => void): void {
        this.onEvent = handler;
    }

    /**
     * Update the panel with new HTML content from the Simple UI backend.
     */
    public updateContent(html: string, theme: string = 'dark'): void {
        if (html !== this.currentHtml) {
            this.currentHtml = html;
            this.panel.webview.html = this.getWrapperHtml(html, theme);
        }
    }

    /**
     * Send a render update via postMessage (incremental update).
     */
    public postRenderUpdate(html: string): void {
        this.panel.webview.postMessage({ type: 'render', html });
    }

    /**
     * Handle messages from the webview.
     */
    private handleWebviewMessage(message: { type: string; [key: string]: unknown }): void {
        if (!this.onEvent) {
            return;
        }

        switch (message.type) {
            case 'keypress':
                this.onEvent('keypress', message.key as string);
                break;
            case 'action':
                this.onEvent('action', message.name as string);
                break;
            case 'resize':
                this.onEvent('resize', `${message.width},${message.height}`);
                break;
            case 'click':
                this.onEvent('click', message.targetId as string);
                break;
        }
    }

    /**
     * Generate the full HTML wrapper for the webview.
     */
    private getWrapperHtml(bodyHtml: string, theme: string): string {
        const nonce = this.getNonce();

        return `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta http-equiv="Content-Security-Policy"
          content="default-src 'none'; style-src 'nonce-${nonce}'; script-src 'nonce-${nonce}';">
    <title>Simple UI</title>
    <style nonce="${nonce}">
        body {
            font-family: var(--vscode-font-family, 'Fira Code', monospace);
            font-size: var(--vscode-font-size, 14px);
            color: var(--vscode-foreground);
            background-color: var(--vscode-editor-background);
            margin: 0;
            padding: 0;
            height: 100vh;
            overflow: hidden;
        }
        #app {
            display: flex;
            flex-direction: column;
            height: 100vh;
        }
        .layout-vbox { display: flex; flex-direction: column; }
        .layout-hbox { display: flex; flex-direction: row; }
        .widget-panel {
            border: 1px solid var(--vscode-panel-border);
            border-radius: 4px;
            background: var(--vscode-editor-background);
            overflow: hidden;
            display: flex;
            flex-direction: column;
        }
        .widget-panel.focused {
            border-color: var(--vscode-focusBorder);
            box-shadow: 0 0 0 1px var(--vscode-focusBorder);
        }
        .panel-title {
            padding: 4px 8px;
            font-weight: bold;
            border-bottom: 1px solid var(--vscode-panel-border);
            font-size: 11px;
            text-transform: uppercase;
            letter-spacing: 0.5px;
            color: var(--vscode-panelTitle-activeForeground);
        }
        .panel-content { padding: 8px; flex: 1; overflow: auto; }
        .widget-text { padding: 4px 8px; }
        .widget-list { list-style: none; padding: 4px 0; }
        .widget-list li { padding: 4px 12px; cursor: pointer; }
        .widget-list li:hover { background: var(--vscode-list-hoverBackground); }
        .widget-button {
            padding: 6px 14px;
            background: var(--vscode-button-background);
            color: var(--vscode-button-foreground);
            border: none;
            border-radius: 2px;
            cursor: pointer;
            font-family: inherit;
        }
        .widget-button:hover { background: var(--vscode-button-hoverBackground); }
        .widget-input, .widget-textfield {
            padding: 6px 12px;
            background: var(--vscode-input-background);
            border: 1px solid var(--vscode-input-border);
            color: var(--vscode-input-foreground);
            font-family: inherit;
            border-radius: 2px;
            width: 100%;
        }
        .widget-input:focus, .widget-textfield:focus {
            outline: none;
            border-color: var(--vscode-focusBorder);
        }
        .widget-statusbar {
            display: flex;
            justify-content: space-between;
            padding: 4px 12px;
            background: var(--vscode-statusBar-background);
            color: var(--vscode-statusBar-foreground);
            font-size: 12px;
        }
        .widget-menubar {
            display: flex;
            padding: 4px 8px;
            background: var(--vscode-titleBar-activeBackground);
            border-bottom: 1px solid var(--vscode-panel-border);
            gap: 4px;
        }
        .widget-tabs { display: flex; border-bottom: 1px solid var(--vscode-panel-border); }
        .tab-item { padding: 6px 16px; cursor: pointer; border-bottom: 2px solid transparent; }
        .tab-item.active { border-bottom-color: var(--vscode-panelTitle-activeBorder); }
        .widget-checkbox { display: flex; align-items: center; gap: 6px; padding: 4px 8px; cursor: pointer; }
        .widget-dropdown {
            padding: 6px 12px;
            background: var(--vscode-dropdown-background);
            border: 1px solid var(--vscode-dropdown-border);
            color: var(--vscode-dropdown-foreground);
            font-family: inherit;
        }
        .widget-progress { padding: 8px; display: flex; align-items: center; gap: 8px; }
        .progress-bar { height: 4px; background: var(--vscode-progressBar-background); border-radius: 2px; }
        .widget-divider { border: none; border-top: 1px solid var(--vscode-panel-border); margin: 8px 0; }
        .widget-dialog {
            position: fixed; top: 50%; left: 50%; transform: translate(-50%, -50%);
            background: var(--vscode-editor-background);
            border: 1px solid var(--vscode-panel-border);
            border-radius: 8px; padding: 0; min-width: 300px;
            box-shadow: 0 4px 16px rgba(0,0,0,0.3);
        }
        .dialog-title { padding: 12px 16px; font-weight: bold; border-bottom: 1px solid var(--vscode-panel-border); }
        .dialog-content { padding: 16px; }
        .empty-state {
            text-align: center;
            color: var(--vscode-descriptionForeground);
            font-style: italic;
            padding: 40px 16px;
        }
    </style>
</head>
<body>
    <div id="app">
        ${bodyHtml || '<div class="empty-state">No UI loaded. Open a .ui.sdn file to preview.</div>'}
    </div>
    <script nonce="${nonce}">
        const vscode = acquireVsCodeApi();

        // Forward keyboard events
        document.addEventListener('keydown', function(e) {
            vscode.postMessage({ type: 'keypress', key: e.key });
        });

        // Forward click events on actionable elements
        document.addEventListener('click', function(e) {
            const actionTarget = e.target.closest('[data-action]');
            if (actionTarget) {
                vscode.postMessage({ type: 'action', name: actionTarget.dataset.action });
                return;
            }
            const idTarget = e.target.closest('[id]');
            if (idTarget) {
                vscode.postMessage({ type: 'click', targetId: idTarget.id });
            }
        });

        // Handle render updates from the extension
        window.addEventListener('message', function(e) {
            const msg = e.data;
            if (msg.type === 'render') {
                document.getElementById('app').innerHTML = msg.html;
            }
        });

        // Report viewport size
        function reportSize() {
            vscode.postMessage({
                type: 'resize',
                width: document.documentElement.clientWidth,
                height: document.documentElement.clientHeight
            });
        }
        window.addEventListener('resize', reportSize);
        reportSize();
    </script>
</body>
</html>`;
    }

    /**
     * Generate a nonce for Content Security Policy.
     */
    private getNonce(): string {
        let text = '';
        const possible = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789';
        for (let i = 0; i < 32; i++) {
            text += possible.charAt(Math.floor(Math.random() * possible.length));
        }
        return text;
    }

    /**
     * Dispose of all resources.
     */
    public dispose(): void {
        SimpleUiPanel.currentPanel = undefined;
        this.panel.dispose();

        for (const disposable of this.disposables) {
            disposable.dispose();
        }
        this.disposables = [];
    }
}
