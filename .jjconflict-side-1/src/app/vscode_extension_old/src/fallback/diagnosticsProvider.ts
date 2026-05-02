/**
 * Fallback Diagnostics Provider
 *
 * Provides basic syntax error detection for .spl files when the LSP
 * server is not available. Detects unclosed brackets, basic syntax
 * errors, and structural issues.
 */

import * as vscode from 'vscode';

export class SimpleDiagnosticsProvider implements vscode.Disposable {
    private diagnosticCollection: vscode.DiagnosticCollection;
    private disposables: vscode.Disposable[] = [];
    private debounceTimers = new Map<string, ReturnType<typeof setTimeout>>();

    constructor() {
        this.diagnosticCollection = vscode.languages.createDiagnosticCollection('simple-fallback');

        // Listen for document changes
        this.disposables.push(
            vscode.workspace.onDidChangeTextDocument(e => {
                if (e.document.languageId === 'simple') {
                    this.debounceDiagnose(e.document);
                }
            })
        );

        // Listen for document open
        this.disposables.push(
            vscode.workspace.onDidOpenTextDocument(doc => {
                if (doc.languageId === 'simple') {
                    this.diagnose(doc);
                }
            })
        );

        // Listen for document close
        this.disposables.push(
            vscode.workspace.onDidCloseTextDocument(doc => {
                this.diagnosticCollection.delete(doc.uri);
                const key = doc.uri.toString();
                const timer = this.debounceTimers.get(key);
                if (timer) {
                    clearTimeout(timer);
                    this.debounceTimers.delete(key);
                }
            })
        );

        // Diagnose all currently open .spl files
        for (const doc of vscode.workspace.textDocuments) {
            if (doc.languageId === 'simple') {
                this.diagnose(doc);
            }
        }
    }

    private debounceDiagnose(document: vscode.TextDocument): void {
        const key = document.uri.toString();
        const existing = this.debounceTimers.get(key);
        if (existing) clearTimeout(existing);

        this.debounceTimers.set(key, setTimeout(() => {
            this.debounceTimers.delete(key);
            this.diagnose(document);
        }, 300));
    }

    diagnose(document: vscode.TextDocument): void {
        const text = document.getText();
        const diagnostics: vscode.Diagnostic[] = [];

        this.checkBrackets(text, document, diagnostics);
        this.checkBasicSyntax(text, document, diagnostics);

        this.diagnosticCollection.set(document.uri, diagnostics);
    }

    private checkBrackets(
        text: string,
        document: vscode.TextDocument,
        diagnostics: vscode.Diagnostic[]
    ): void {
        const stack: { char: string; pos: number }[] = [];
        const pairs: Record<string, string> = { '(': ')', '[': ']', '{': '}' };
        const closing: Record<string, string> = { ')': '(', ']': '[', '}': '{' };
        let inString = false;
        let stringChar = '';
        let inComment = false;
        let inBlockComment = false;

        for (let i = 0; i < text.length; i++) {
            const ch = text[i];

            // Block comment
            if (inBlockComment) {
                if (ch === '*' && text[i + 1] === '/') {
                    inBlockComment = false;
                    i++;
                }
                continue;
            }
            if (ch === '/' && text[i + 1] === '*') {
                inBlockComment = true;
                i++;
                continue;
            }

            // Line comment
            if (inComment) {
                if (ch === '\n') inComment = false;
                continue;
            }
            if (ch === '#') {
                inComment = true;
                continue;
            }

            // Strings
            if (inString) {
                if (ch === '\\') { i++; continue; }
                if (ch === stringChar) inString = false;
                continue;
            }
            if (ch === '"' || ch === "'") {
                inString = true;
                stringChar = ch;
                continue;
            }

            // Brackets
            if (pairs[ch]) {
                stack.push({ char: ch, pos: i });
            } else if (closing[ch]) {
                if (stack.length === 0 || stack[stack.length - 1].char !== closing[ch]) {
                    const pos = document.positionAt(i);
                    diagnostics.push(new vscode.Diagnostic(
                        new vscode.Range(pos, pos.translate(0, 1)),
                        `Unexpected '${ch}'`,
                        vscode.DiagnosticSeverity.Error
                    ));
                } else {
                    stack.pop();
                }
            }
        }

        // Report unclosed brackets
        for (const item of stack) {
            const pos = document.positionAt(item.pos);
            diagnostics.push(new vscode.Diagnostic(
                new vscode.Range(pos, pos.translate(0, 1)),
                `Unclosed '${item.char}'`,
                vscode.DiagnosticSeverity.Error
            ));
        }
    }

    private checkBasicSyntax(
        text: string,
        document: vscode.TextDocument,
        diagnostics: vscode.Diagnostic[]
    ): void {
        const lines = text.split('\n');

        for (let i = 0; i < lines.length; i++) {
            const line = lines[i];
            const trimmed = line.trimStart();

            // Skip comments and empty lines
            if (!trimmed || trimmed.startsWith('#') || trimmed.startsWith('/*') || trimmed.startsWith('*')) {
                continue;
            }

            // Check for consecutive operators that are likely errors
            const doubleOp = trimmed.match(/[=+\-*/%](\s*)[=+\-*/%]{2,}/);
            if (doubleOp) {
                // Allow ==, !=, <=, >=, **, ->, =>, +=, -=, *=, /=, ++, --
                const full = trimmed.substring(doubleOp.index || 0);
                if (!/^(==|!=|<=|>=|\*\*|->|=>|\+=|-=|\*=|\/=|%=|\+\+|--)/.test(full.trimStart())) {
                    const charIdx = line.indexOf(doubleOp[0]);
                    if (charIdx >= 0) {
                        diagnostics.push(new vscode.Diagnostic(
                            new vscode.Range(i, charIdx, i, charIdx + doubleOp[0].length),
                            `Unexpected operator sequence`,
                            vscode.DiagnosticSeverity.Error
                        ));
                    }
                }
            }

            // Check for trailing operator at end of non-continued line (= + - * / without \)
            if (/[+\-*/%]\s*$/.test(trimmed) && !trimmed.endsWith('\\')) {
                // Allow lines ending with : (block start), or lines that are just operators
                // Only flag if line has meaningful content before the operator
                const beforeOp = trimmed.replace(/[+\-*/%]\s*$/, '').trim();
                if (beforeOp && !beforeOp.endsWith(':') && !beforeOp.endsWith(',')) {
                    // Check next line exists and has content (continuation)
                    const nextLine = i + 1 < lines.length ? lines[i + 1].trim() : '';
                    if (!nextLine) {
                        const opMatch = trimmed.match(/([+\-*/%])\s*$/);
                        if (opMatch) {
                            const charIdx = line.lastIndexOf(opMatch[1]);
                            diagnostics.push(new vscode.Diagnostic(
                                new vscode.Range(i, charIdx, i, charIdx + 1),
                                `Trailing operator '${opMatch[1]}' at end of file`,
                                vscode.DiagnosticSeverity.Warning
                            ));
                        }
                    }
                }
            }
        }
    }

    dispose(): void {
        this.diagnosticCollection.dispose();
        for (const d of this.disposables) d.dispose();
        for (const timer of this.debounceTimers.values()) clearTimeout(timer);
        this.debounceTimers.clear();
    }
}
