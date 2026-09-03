import * as path from 'path';
import * as vscode from 'vscode';

export interface VsCodeStorageRoots {
    userRoot: string;
    worktreeRoot: string;
}

export function resolveVsCodeStorageRoots(
    context: vscode.ExtensionContext | undefined,
    workspaceRoot: string | undefined,
    environment: NodeJS.ProcessEnv = process.env,
): VsCodeStorageRoots | undefined {
    const userRoot = environment.SIMPLE_USER_STORAGE_ROOT?.trim()
        || (context ? path.join(context.globalStorageUri.fsPath, 'storage') : '');
    const worktreeRoot = environment.SIMPLE_WORKTREE_STORAGE_ROOT?.trim()
        || (workspaceRoot ? path.join(workspaceRoot, '.simple', 'storage') : '');
    if (!userRoot || !worktreeRoot) {
        return undefined;
    }
    return {
        userRoot: path.resolve(userRoot),
        worktreeRoot: path.resolve(worktreeRoot),
    };
}

export function projectSimpleToolEnvironment(
    roots: VsCodeStorageRoots,
    base: NodeJS.ProcessEnv = process.env,
): NodeJS.ProcessEnv {
    const environment = { ...base };
    delete environment.TMP;
    delete environment.TEMP;
    environment.SIMPLE_USER_STORAGE_ROOT = roots.userRoot;
    environment.SIMPLE_WORKTREE_STORAGE_ROOT = roots.worktreeRoot;
    environment.SIMPLE_CACHE = path.join(roots.userRoot, 'cache', 'simple', 'compiler-v1');
    environment.SIMPLE_FRONTEND_CACHE_DIR = path.join(roots.userRoot, 'cache', 'simple', 'frontend-v1');
    environment.SIMPLE_HIR_CACHE_DIR = path.join(roots.userRoot, 'cache', 'simple', 'hir-v1');
    environment.SIMPLE_NATIVE_BUILD_CACHE_DIR = path.join(roots.worktreeRoot, 'build', 'simple');
    environment.SIMPLE_TEST_TMP = path.join(roots.worktreeRoot, 'tmp', 'vscode');
    environment.TMPDIR = environment.SIMPLE_TEST_TMP;
    return environment;
}
