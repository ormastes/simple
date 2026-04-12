import * as vscode from 'vscode';
import { ExtensionHostServices } from '../services/extensionHostServices';
import { SimpleCliService } from '../services/simpleCliService';
export declare class SimpleTestController implements vscode.Disposable {
    private readonly cli;
    private readonly services;
    private readonly controller;
    private readonly output;
    private readonly profile;
    private readonly disposables;
    constructor(cli: SimpleCliService, services: ExtensionHostServices);
    getController(): vscode.TestController;
    refreshWorkspace(): Promise<void>;
    dispose(): void;
    private refreshUri;
    private refreshDocument;
    private runTests;
    private collectFileItems;
    private runFileItem;
}
