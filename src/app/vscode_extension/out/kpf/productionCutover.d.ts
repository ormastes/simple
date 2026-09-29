export type KpfToolingPlacement = 'native-process' | 'worker-process' | 'wasm';
export type KpfSemanticAuthority = 'toolingd-lsp' | 'syntax-only-fallback';
export interface KpfBootstrapResult {
    readonly ok: boolean;
    readonly message: string;
    readonly detail?: string;
}
export interface KpfProductionCutoverOptions {
    readonly languageId: string;
    readonly isWorkspaceTrusted: () => boolean;
    readonly resolvePlacement: () => KpfToolingPlacement;
    readonly bootstrap: (resolveFrom?: string) => Promise<KpfBootstrapResult>;
    readonly restart: () => Promise<KpfBootstrapResult>;
    readonly onAuthorityChanged?: (authority: KpfSemanticAuthority, reason: string) => void;
}
export declare class KpfProductionCutover {
    private readonly options;
    private observedResolveFrom;
    private languageObserved;
    private bootstrapPromise;
    private authority;
    constructor(options: KpfProductionCutoverOptions);
    observeLanguage(languageId: string, resolveFrom?: string): Promise<KpfBootstrapResult> | undefined;
    workspaceTrustGranted(): Promise<KpfBootstrapResult> | undefined;
    restart(): Promise<KpfBootstrapResult>;
    semanticAuthority(): KpfSemanticAuthority;
    private ensureAuthoritative;
    private trustFailure;
    private applyResult;
    private publishAuthority;
}
