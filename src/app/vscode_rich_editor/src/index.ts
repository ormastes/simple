/**
 * Rich editor module barrel — activation entry point.
 */

import * as vscode from 'vscode';
import { RichCustomEditorProvider } from './richCustomEditor';

export function activateRichEditorFeatures(context: vscode.ExtensionContext): void {
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
            const editor = vscode.window.activeTextEditor;
            if (editor) {
                void vscode.commands.executeCommand(
                    'vscode.openWith',
                    editor.document.uri,
                    RichCustomEditorProvider.viewType,
                );
            }
        }),
    );
}
