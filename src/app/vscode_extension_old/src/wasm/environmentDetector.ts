/**
 * Environment Detector - Detects desktop vs. web VSCode environment
 *
 * Determines whether the extension is running in:
 * - Desktop VSCode (native process execution available)
 * - VSCode Web (vscode.dev, github.dev - WASM only)
 * - Remote (SSH, WSL, Codespaces - native available on remote)
 */

import * as vscode from 'vscode';

export enum EnvironmentKind {
    /** Desktop VSCode - native LSP binary available */
    Desktop = 'desktop',
    /** VSCode Web (vscode.dev, github.dev) - WASM only */
    Web = 'web',
    /** Remote environment (SSH, WSL, Codespaces) - native on remote */
    Remote = 'remote',
}

/**
 * LSP mode selection.
 */
export enum LspMode {
    /** Auto-detect: native on desktop/remote, WASM on web */
    Auto = 'auto',
    /** Force native LSP binary (subprocess) */
    Native = 'native',
    /** Force WASM LSP (in-process) */
    Wasm = 'wasm',
}

/**
 * Detect the current VSCode environment.
 */
export function detectEnvironment(): EnvironmentKind {
    // Check for web environment
    if (vscode.env.uiKind === vscode.UIKind.Web) {
        return EnvironmentKind.Web;
    }

    // Check for remote environment
    if (vscode.env.remoteName) {
        return EnvironmentKind.Remote;
    }

    return EnvironmentKind.Desktop;
}

/**
 * Determine the LSP mode based on environment and user settings.
 */
export function determineLspMode(): LspMode {
    const config = vscode.workspace.getConfiguration('simple');
    const userMode = config.get<string>('lsp.mode', 'auto');

    switch (userMode) {
        case 'native':
            return LspMode.Native;
        case 'wasm':
            return LspMode.Wasm;
        default:
            return LspMode.Auto;
    }
}

/**
 * Determine whether to use WASM based on environment and user preference.
 */
export function shouldUseWasm(): boolean {
    const mode = determineLspMode();
    const env = detectEnvironment();

    switch (mode) {
        case LspMode.Native:
            return false;
        case LspMode.Wasm:
            return true;
        case LspMode.Auto:
            // Web environment always uses WASM
            return env === EnvironmentKind.Web;
    }
}

/**
 * Get a human-readable description of the current environment.
 */
export function getEnvironmentDescription(): string {
    const env = detectEnvironment();
    const mode = determineLspMode();
    const useWasm = shouldUseWasm();

    return `Environment: ${env}, Mode: ${mode}, Using WASM: ${useWasm}`;
}
