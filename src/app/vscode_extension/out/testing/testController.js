"use strict";
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
exports.SimpleTestController = void 0;
const vscode = __importStar(require("vscode"));
const testDiscovery_1 = require("./testDiscovery");
function createTestId(uri, label, line) {
    return `${uri.toString()}::${label}::${line}`;
}
function isDoctestBlock(block) {
    return block.kind === 'sdoctest';
}
function collectItems(collection) {
    const items = [];
    collection.forEach((item) => {
        items.push(item);
    });
    return items;
}
class SimpleTestController {
    constructor(cli, services) {
        this.cli = cli;
        this.services = services;
        this.output = vscode.window.createOutputChannel('Simple Test Runner');
        this.disposables = [];
        this.controller = vscode.tests.createTestController('simpleTests', 'Simple Tests');
        this.controller.resolveHandler = async (item) => {
            if (item) {
                await this.refreshUri(item.uri ?? vscode.Uri.parse(item.id.split('::')[0]));
                return;
            }
            await this.refreshWorkspace();
        };
        this.profile = this.controller.createRunProfile('Run', vscode.TestRunProfileKind.Run, (request, token) => void this.runTests(request, token), true);
        this.disposables.push(this.controller, this.profile, this.output, vscode.workspace.onDidOpenTextDocument((document) => {
            if (document.languageId === 'simple') {
                void this.refreshDocument(document);
            }
        }), vscode.workspace.onDidChangeTextDocument((event) => {
            if (event.document.languageId === 'simple') {
                void this.refreshDocument(event.document);
            }
        }), vscode.workspace.onDidDeleteFiles((event) => {
            for (const uri of event.files) {
                this.controller.items.delete(uri.toString());
            }
        }));
        for (const document of vscode.workspace.textDocuments) {
            if (document.languageId === 'simple') {
                void this.refreshDocument(document);
            }
        }
    }
    getController() {
        return this.controller;
    }
    async refreshWorkspace() {
        const uris = await vscode.workspace.findFiles('**/*.spl', '**/{node_modules,out,.git,target,build}/**', 200);
        for (const uri of uris) {
            await this.refreshUri(uri);
        }
    }
    dispose() {
        for (const disposable of this.disposables) {
            disposable.dispose();
        }
    }
    async refreshUri(uri) {
        try {
            const document = await vscode.workspace.openTextDocument(uri);
            await this.refreshDocument(document);
        }
        catch {
            this.controller.items.delete(uri.toString());
        }
    }
    async refreshDocument(document) {
        if (document.languageId !== 'simple') {
            return;
        }
        const fileId = document.uri.toString();
        const fileItem = this.controller.items.get(fileId)
            ?? this.controller.createTestItem(fileId, document.fileName.split(/[\\/]/).pop() ?? document.fileName, document.uri);
        fileItem.canResolveChildren = false;
        this.controller.items.add(fileItem);
        fileItem.children.replace([]);
        for (const block of (0, testDiscovery_1.detectTestBlocks)(document)) {
            const child = this.controller.createTestItem(createTestId(document.uri, block.label, block.line), block.label, document.uri);
            child.range = new vscode.Range(block.line, 0, block.line, document.lineAt(block.line).text.length);
            fileItem.children.add(child);
        }
    }
    async runTests(request, token) {
        const run = this.controller.createTestRun(request);
        const fileItems = this.collectFileItems(request);
        try {
            this.services.setStatus('tests', { health: 'starting', source: 'native', message: 'Running Simple tests' });
            for (const fileItem of fileItems) {
                await this.runFileItem(fileItem, run, token);
            }
            this.services.markReady('tests', `Ran ${fileItems.length} test file(s)`);
        }
        catch (error) {
            const detail = error instanceof Error ? error.message : String(error);
            this.services.markDegraded('tests', 'Test run failed', 'native', detail);
        }
        finally {
            run.end();
        }
    }
    collectFileItems(request) {
        const included = request.include && request.include.length > 0
            ? request.include
            : collectItems(this.controller.items);
        const fileMap = new Map();
        for (const item of included) {
            const fileItem = item.parent ?? item;
            fileMap.set(fileItem.id, fileItem);
        }
        return Array.from(fileMap.values()).filter((item) => item.uri);
    }
    async runFileItem(fileItem, run, token) {
        const childItems = collectItems(fileItem.children);
        run.enqueued(fileItem);
        run.started(fileItem);
        for (const child of childItems) {
            run.enqueued(child);
            run.started(child);
        }
        const hasDoctestOnlyChildren = childItems.length > 0 && childItems.every((child) => child.label === 'sdoctest');
        const args = hasDoctestOnlyChildren
            ? ['test', '--sdoctest', fileItem.uri.fsPath]
            : ['test', fileItem.uri.fsPath];
        const result = await this.cli.run(args, { cwd: vscode.workspace.workspaceFolders?.[0]?.uri.fsPath, token });
        const duration = Math.max(1, result.combined.length > 0 ? result.combined.length : 1);
        this.output.appendLine(`$ simple ${args.join(' ')}`);
        if (result.stdout.trim()) {
            this.output.appendLine(result.stdout.trim());
        }
        if (result.stderr.trim()) {
            this.output.appendLine(result.stderr.trim());
        }
        run.appendOutput(`${result.combined || '(no output)'}\n`, undefined, fileItem);
        if (result.exitCode === 0) {
            run.passed(fileItem, duration);
            for (const child of childItems) {
                run.passed(child, duration);
            }
        }
        else {
            const message = new vscode.TestMessage(result.combined || 'Simple test command failed');
            run.failed(fileItem, message, duration);
            for (const child of childItems) {
                run.failed(child, message, duration);
            }
        }
    }
}
exports.SimpleTestController = SimpleTestController;
//# sourceMappingURL=testController.js.map