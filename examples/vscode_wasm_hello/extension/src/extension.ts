import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';

let panel: vscode.WebviewPanel | undefined;

export function activate(context: vscode.ExtensionContext) {
    context.subscriptions.push(
        vscode.commands.registerCommand('simpleWasmHello.showPanel', () => {
            if (panel) {
                panel.reveal();
                return;
            }

            panel = vscode.window.createWebviewPanel(
                'simpleWasmHello',
                'Simple WASM Hello',
                vscode.ViewColumn.One,
                { enableScripts: true, localResourceRoots: [vscode.Uri.file(path.join(context.extensionPath, 'wasm'))] }
            );

            const wasmPath = path.join(context.extensionPath, 'wasm', 'hello.wasm');
            const wasmBytes = fs.readFileSync(wasmPath);
            const wasmBase64 = wasmBytes.toString('base64');

            panel.webview.html = `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta http-equiv="Content-Security-Policy" content="default-src 'none'; script-src 'unsafe-inline'; style-src 'unsafe-inline';">
    <title>Simple WASM Hello</title>
    <style>
        body { font-family: var(--vscode-font-family); color: var(--vscode-foreground); background: var(--vscode-editor-background); padding: 24px; }
        h1 { font-size: 20px; margin-bottom: 16px; }
        .result { background: var(--vscode-textBlockQuote-background); border-radius: 4px; padding: 12px 16px; margin: 8px 0; font-family: var(--vscode-editor-font-family); }
        .label { color: var(--vscode-descriptionForeground); font-size: 12px; margin-bottom: 4px; }
        .value { font-size: 16px; font-weight: bold; }
        .error { color: var(--vscode-errorForeground); }
    </style>
</head>
<body>
    <h1>Hello from Simple WASM!</h1>
    <div id="output"></div>
    <script>
        (async () => {
            const out = document.getElementById('output');
            try {
                const b64 = "${wasmBase64}";
                const bytes = Uint8Array.from(atob(b64), c => c.charCodeAt(0));
                const { instance } = await WebAssembly.instantiate(bytes);
                const ex = instance.exports;

                const results = [
                    ['hello()', ex.hello()],
                    ['add(3, 4)', ex.add(3, 4)],
                    ['factorial(10)', ex.factorial(10)],
                ];

                out.innerHTML = results.map(([call, val]) =>
                    '<div class="result"><div class="label">' + call + '</div><div class="value">' + val + '</div></div>'
                ).join('');
            } catch (e) {
                out.innerHTML = '<div class="result error">' + e.message + '</div>';
            }
        })();
    </script>
</body>
</html>`;

            panel.onDidDispose(() => { panel = undefined; });
        })
    );
}

export function deactivate() {}
