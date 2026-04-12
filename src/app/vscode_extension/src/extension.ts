/**
 * Simple Rich Editor — standalone VSCode extension entry point.
 */

import * as vscode from 'vscode';
import { RichCustomEditorProvider } from './richCustomEditor';

async function reopenActiveSimpleDocumentWithRichEditor(): Promise<void> {
    const editor = vscode.window.activeTextEditor;
    if (!editor) return;

    const document = editor.document;
    const isSimpleFile = document.languageId === 'simple' || document.uri.fsPath.endsWith('.spl');
    if (!isSimpleFile) return;

    await vscode.commands.executeCommand(
        'vscode.openWith',
        document.uri,
        RichCustomEditorProvider.viewType,
    );
}

export function activate(context: vscode.ExtensionContext) {
    console.log('Simple Rich Editor activating...');

    context.subscriptions.push(
        vscode.window.registerCustomEditorProvider(
            RichCustomEditorProvider.viewType,
            new RichCustomEditorProvider(context.extensionUri),
            {
                webviewOptions: { retainContextWhenHidden: true },
                supportsMultipleEditorsPerDocument: false,
            },
        ),
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('simple.richEditor.open', () => {
            void reopenActiveSimpleDocumentWithRichEditor();
        }),
    );

    void reopenActiveSimpleDocumentWithRichEditor();

    console.log('Simple Rich Editor activated');
}

export function deactivate() {}
