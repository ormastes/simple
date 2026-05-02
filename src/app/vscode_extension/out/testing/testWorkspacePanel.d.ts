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
}
export declare class TestWorkspacePanel implements vscode.Disposable {
    static currentPanel: TestWorkspacePanel | undefined;
    private readonly panel;
    private readonly disposables;
    private entries;
    private constructor();
    static show(extensionUri: vscode.Uri): TestWorkspacePanel;
    refresh(): void;
    openLatestArtifacts(): void;
    dispose(): void;
    private handleMessage;
    private openSource;
    private openArtifacts;
    private rerun;
}
