/**
 * Environment Detector - Detects desktop vs. web VSCode environment
 *
 * Determines whether the extension is running in:
 * - Desktop VSCode (native process execution available)
 * - VSCode Web (vscode.dev, github.dev - WASM only)
 * - Remote (SSH, WSL, Codespaces - native available on remote)
 */
export declare enum EnvironmentKind {
    /** Desktop VSCode - native LSP binary available */
    Desktop = "desktop",
    /** VSCode Web (vscode.dev, github.dev) - WASM only */
    Web = "web",
    /** Remote environment (SSH, WSL, Codespaces) - native on remote */
    Remote = "remote"
}
/**
 * LSP mode selection.
 */
export declare enum LspMode {
    /** Auto-detect: native on desktop/remote, WASM on web */
    Auto = "auto",
    /** Force native LSP binary (subprocess) */
    Native = "native",
    /** Force WASM LSP (in-process) */
    Wasm = "wasm"
}
/**
 * Detect the current VSCode environment.
 */
export declare function detectEnvironment(): EnvironmentKind;
/**
 * Determine the LSP mode based on environment and user settings.
 */
export declare function determineLspMode(): LspMode;
/**
 * Determine whether to use WASM based on environment and user preference.
 */
export declare function shouldUseWasm(): boolean;
/**
 * Get a human-readable description of the current environment.
 */
export declare function getEnvironmentDescription(): string;
