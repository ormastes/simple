import * as vscode from 'vscode';
export interface TestWorkspaceEntry {
    sourcePath: string;
    artifactDirectory: string;
    resultJsonPath: string;
    status: string;
    passed: number;
    failed: number;
    skipped: number;
    ignored: number;
    durationMs: number;
    updatedAt: number;
    label: string;
    artifactRoots: string[];
}
export declare function discoverTestWorkspaceEntries(workspaceFolders: readonly vscode.WorkspaceFolder[] | undefined): TestWorkspaceEntry[];
export declare function buildTestWorkspaceHtml(entries: TestWorkspaceEntry[]): string;
export declare class TestWorkspacePanel implements vscode.Disposable {
    static currentPanel: TestWorkspacePanel | undefined;
    private readonly panel;
    private readonly extensionUri;
    private readonly disposables;
    private entries;
    private constructor();
    static show(extensionUri: vscode.Uri): TestWorkspacePanel;
    static isVisible(): boolean;
    static close(): void;
    refresh(): void;
    private handleMessage;
    private openSource;
    private openArtifacts;
    private rerun;
    openLatestArtifacts(): void;
    dispose(): void;
}
