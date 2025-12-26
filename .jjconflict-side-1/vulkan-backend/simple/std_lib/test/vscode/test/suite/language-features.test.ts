import * as assert from 'assert';
import * as vscode from 'vscode';

suite('Definition Provider Test Suite', () => {
    test('Can execute go-to-definition', async () => {
        const doc = await vscode.workspace.openTextDocument({
            language: 'simple',
            content: 'fn greet(name: String):\n    print(name)\n\ngreet("Alice")',
        });

        await vscode.window.showTextDocument(doc);

        const position = new vscode.Position(3, 0); // Position on 'greet' call

        const definitions = await vscode.commands.executeCommand<vscode.Location[]>(
            'vscode.executeDefinitionProvider',
            doc.uri,
            position
        );

        // Definition provider might return locations
        assert.ok(Array.isArray(definitions), 'Definitions should be an array');

        await vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Can register definition provider', () => {
        let providerDisposable: vscode.Disposable | undefined;

        try {
            const provider: vscode.DefinitionProvider = {
                provideDefinition(
                    document: vscode.TextDocument,
                    position: vscode.Position
                ): vscode.Location | undefined {
                    // Example: Find function definition
                    const wordRange = document.getWordRangeAtPosition(position);
                    if (!wordRange) {
                        return undefined;
                    }

                    const word = document.getText(wordRange);

                    // Simple heuristic: find 'fn <word>'
                    const text = document.getText();
                    const fnPattern = new RegExp(`fn\\s+${word}\\s*\\(`);
                    const match = fnPattern.exec(text);

                    if (match) {
                        const pos = document.positionAt(match.index);
                        return new vscode.Location(document.uri, pos);
                    }

                    return undefined;
                }
            };

            providerDisposable = vscode.languages.registerDefinitionProvider(
                { language: 'simple' },
                provider
            );

            assert.ok(providerDisposable, 'Definition provider should be registered');
        } finally {
            providerDisposable?.dispose();
        }
    });
});

suite('References Provider Test Suite', () => {
    test('Can execute find-references', async () => {
        const doc = await vscode.workspace.openTextDocument({
            language: 'simple',
            content: 'fn test():\n    let x = 10\n    print(x)\n    return x',
        });

        await vscode.window.showTextDocument(doc);

        const position = new vscode.Position(1, 8); // Position on 'x' declaration

        const references = await vscode.commands.executeCommand<vscode.Location[]>(
            'vscode.executeReferenceProvider',
            doc.uri,
            position
        );

        assert.ok(Array.isArray(references), 'References should be an array');

        await vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Can register references provider', () => {
        let providerDisposable: vscode.Disposable | undefined;

        try {
            const provider: vscode.ReferenceProvider = {
                provideReferences(
                    document: vscode.TextDocument,
                    position: vscode.Position,
                    context: vscode.ReferenceContext
                ): vscode.Location[] {
                    const locations: vscode.Location[] = [];

                    const wordRange = document.getWordRangeAtPosition(position);
                    if (!wordRange) {
                        return locations;
                    }

                    const word = document.getText(wordRange);

                    // Simple search for all occurrences
                    const text = document.getText();
                    const regex = new RegExp(`\\b${word}\\b`, 'g');
                    let match;

                    while ((match = regex.exec(text)) !== null) {
                        const pos = document.positionAt(match.index);
                        locations.push(new vscode.Location(document.uri, pos));
                    }

                    return locations;
                }
            };

            providerDisposable = vscode.languages.registerReferenceProvider(
                { language: 'simple' },
                provider
            );

            assert.ok(providerDisposable, 'References provider should be registered');
        } finally {
            providerDisposable?.dispose();
        }
    });
});

suite('Document Symbols Test Suite', () => {
    test('Can execute document symbols', async () => {
        const doc = await vscode.workspace.openTextDocument({
            language: 'simple',
            content: 'fn main():\n    pass\n\nclass Person:\n    fn __init__(name: String):\n        self.name = name',
        });

        await vscode.window.showTextDocument(doc);

        const symbols = await vscode.commands.executeCommand<vscode.DocumentSymbol[]>(
            'vscode.executeDocumentSymbolProvider',
            doc.uri
        );

        assert.ok(Array.isArray(symbols), 'Symbols should be an array');

        await vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Can register document symbol provider', () => {
        let providerDisposable: vscode.Disposable | undefined;

        try {
            const provider: vscode.DocumentSymbolProvider = {
                provideDocumentSymbols(document: vscode.TextDocument): vscode.DocumentSymbol[] {
                    const symbols: vscode.DocumentSymbol[] = [];
                    const text = document.getText();

                    // Find functions
                    const fnRegex = /fn\s+(\w+)\s*\(/g;
                    let match;

                    while ((match = fnRegex.exec(text)) !== null) {
                        const name = match[1];
                        const pos = document.positionAt(match.index);
                        const range = new vscode.Range(pos, pos.translate(0, match[0].length));

                        const symbol = new vscode.DocumentSymbol(
                            name,
                            'function',
                            vscode.SymbolKind.Function,
                            range,
                            range
                        );

                        symbols.push(symbol);
                    }

                    // Find classes
                    const classRegex = /class\s+(\w+)/g;

                    while ((match = classRegex.exec(text)) !== null) {
                        const name = match[1];
                        const pos = document.positionAt(match.index);
                        const range = new vscode.Range(pos, pos.translate(0, match[0].length));

                        const symbol = new vscode.DocumentSymbol(
                            name,
                            'class',
                            vscode.SymbolKind.Class,
                            range,
                            range
                        );

                        symbols.push(symbol);
                    }

                    return symbols;
                }
            };

            providerDisposable = vscode.languages.registerDocumentSymbolProvider(
                { language: 'simple' },
                provider
            );

            assert.ok(providerDisposable, 'Document symbol provider should be registered');
        } finally {
            providerDisposable?.dispose();
        }
    });

    test('DocumentSymbol has correct properties', () => {
        const range = new vscode.Range(0, 0, 2, 0);
        const selectionRange = new vscode.Range(0, 3, 0, 7);

        const symbol = new vscode.DocumentSymbol(
            'main',
            'entry point',
            vscode.SymbolKind.Function,
            range,
            selectionRange
        );

        assert.strictEqual(symbol.name, 'main');
        assert.strictEqual(symbol.detail, 'entry point');
        assert.strictEqual(symbol.kind, vscode.SymbolKind.Function);
        assert.ok(symbol.range.isEqual(range));
        assert.ok(symbol.selectionRange.isEqual(selectionRange));
    });

    test('Can create nested symbols', () => {
        const classRange = new vscode.Range(0, 0, 5, 0);
        const classSelection = new vscode.Range(0, 6, 0, 12);

        const classSymbol = new vscode.DocumentSymbol(
            'Person',
            '',
            vscode.SymbolKind.Class,
            classRange,
            classSelection
        );

        const methodRange = new vscode.Range(1, 4, 3, 0);
        const methodSelection = new vscode.Range(1, 7, 1, 15);

        const methodSymbol = new vscode.DocumentSymbol(
            '__init__',
            'constructor',
            vscode.SymbolKind.Constructor,
            methodRange,
            methodSelection
        );

        classSymbol.children = [methodSymbol];

        assert.strictEqual(classSymbol.children.length, 1);
        assert.strictEqual(classSymbol.children[0].name, '__init__');
        assert.strictEqual(classSymbol.children[0].kind, vscode.SymbolKind.Constructor);
    });
});

suite('Workspace Symbols Test Suite', () => {
    test('Can execute workspace symbols', async () => {
        const symbols = await vscode.commands.executeCommand<vscode.SymbolInformation[]>(
            'vscode.executeWorkspaceSymbolProvider',
            'test'
        );

        assert.ok(Array.isArray(symbols), 'Workspace symbols should be an array');
    });

    test('Can register workspace symbol provider', () => {
        let providerDisposable: vscode.Disposable | undefined;

        try {
            const provider: vscode.WorkspaceSymbolProvider = {
                provideWorkspaceSymbols(query: string): vscode.SymbolInformation[] {
                    const symbols: vscode.SymbolInformation[] = [];

                    // Example: Return dummy symbols for testing
                    if (query.includes('test')) {
                        const uri = vscode.Uri.file('/dummy/test.spl');
                        const location = new vscode.Location(uri, new vscode.Position(0, 0));

                        symbols.push(new vscode.SymbolInformation(
                            'test_function',
                            vscode.SymbolKind.Function,
                            'Tests',
                            location
                        ));
                    }

                    return symbols;
                }
            };

            providerDisposable = vscode.languages.registerWorkspaceSymbolProvider(provider);

            assert.ok(providerDisposable, 'Workspace symbol provider should be registered');
        } finally {
            providerDisposable?.dispose();
        }
    });
});

suite('Signature Help Test Suite', () => {
    test('Can execute signature help', async () => {
        const doc = await vscode.workspace.openTextDocument({
            language: 'simple',
            content: 'fn greet(name: String, age: i64):\n    pass\n\ngreet(',
        });

        await vscode.window.showTextDocument(doc);

        const position = new vscode.Position(3, 6); // Inside function call

        const help = await vscode.commands.executeCommand<vscode.SignatureHelp>(
            'vscode.executeSignatureHelpProvider',
            doc.uri,
            position
        );

        // Signature help might be provided
        assert.ok(help === undefined || help.signatures !== undefined, 'Help should be valid or undefined');

        await vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Can register signature help provider', () => {
        let providerDisposable: vscode.Disposable | undefined;

        try {
            const provider: vscode.SignatureHelpProvider = {
                provideSignatureHelp(
                    document: vscode.TextDocument,
                    position: vscode.Position
                ): vscode.SignatureHelp | undefined {
                    // Example: Provide signature for 'greet' function
                    const lineText = document.lineAt(position.line).text;

                    if (lineText.includes('greet(')) {
                        const help = new vscode.SignatureHelp();

                        const signature = new vscode.SignatureInformation(
                            'greet(name: String, age: i64)',
                            'Greets a person with their name and age'
                        );

                        signature.parameters = [
                            new vscode.ParameterInformation('name: String', 'The person\'s name'),
                            new vscode.ParameterInformation('age: i64', 'The person\'s age')
                        ];

                        help.signatures = [signature];
                        help.activeSignature = 0;
                        help.activeParameter = 0;

                        return help;
                    }

                    return undefined;
                }
            };

            providerDisposable = vscode.languages.registerSignatureHelpProvider(
                { language: 'simple' },
                provider,
                '(', ','
            );

            assert.ok(providerDisposable, 'Signature help provider should be registered');
        } finally {
            providerDisposable?.dispose();
        }
    });
});
