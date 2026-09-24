import * as vscode from 'vscode';
export interface VsCodeStorageRoots {
    userRoot: string;
    worktreeRoot: string;
}
export declare function resolveVsCodeStorageRoots(context: vscode.ExtensionContext | undefined, workspaceRoot: string | undefined, environment?: NodeJS.ProcessEnv): VsCodeStorageRoots | undefined;
export declare function projectSimpleToolEnvironment(roots: VsCodeStorageRoots, base?: NodeJS.ProcessEnv): NodeJS.ProcessEnv;
