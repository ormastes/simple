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

export class KpfProductionCutover {
    private observedResolveFrom: string | undefined;
    private languageObserved = false;
    private bootstrapPromise: Promise<KpfBootstrapResult> | undefined;
    private authority: KpfSemanticAuthority = 'syntax-only-fallback';

    public constructor(private readonly options: KpfProductionCutoverOptions) {
        this.publishAuthority('Syntax-only fallback active until the shared tooling service is admitted');
    }

    public observeLanguage(languageId: string, resolveFrom?: string): Promise<KpfBootstrapResult> | undefined {
        if (languageId !== this.options.languageId) {
            return undefined;
        }
        this.languageObserved = true;
        this.observedResolveFrom = resolveFrom ?? this.observedResolveFrom;
        return this.ensureAuthoritative();
    }

    public workspaceTrustGranted(): Promise<KpfBootstrapResult> | undefined {
        if (!this.languageObserved) {
            return undefined;
        }
        return this.ensureAuthoritative();
    }

    public async restart(): Promise<KpfBootstrapResult> {
        const blocked = this.trustFailure();
        if (blocked) {
            this.publishAuthority(blocked.message);
            return blocked;
        }
        const result = await this.options.restart();
        this.applyResult(result);
        return result;
    }

    public semanticAuthority(): KpfSemanticAuthority {
        return this.authority;
    }

    private ensureAuthoritative(): Promise<KpfBootstrapResult> {
        const blocked = this.trustFailure();
        if (blocked) {
            this.publishAuthority(blocked.message);
            return Promise.resolve(blocked);
        }
        if (!this.bootstrapPromise) {
            this.bootstrapPromise = this.options.bootstrap(this.observedResolveFrom)
                .then((result) => {
                    this.applyResult(result);
                    if (!result.ok) {
                        this.bootstrapPromise = undefined;
                    }
                    return result;
                })
                .catch((error: unknown) => {
                    const result: KpfBootstrapResult = {
                        ok: false,
                        message: 'Shared tooling service failed to start; syntax-only fallback remains active',
                        detail: error instanceof Error ? error.message : String(error),
                    };
                    this.applyResult(result);
                    this.bootstrapPromise = undefined;
                    return result;
                });
        }
        return this.bootstrapPromise;
    }

    private trustFailure(): KpfBootstrapResult | undefined {
        const placement = this.options.resolvePlacement();
        if (placement === 'wasm' || this.options.isWorkspaceTrusted()) {
            return undefined;
        }
        return {
            ok: false,
            message: `Workspace trust is required for ${placement}; syntax-only fallback remains active`,
        };
    }

    private applyResult(result: KpfBootstrapResult): void {
        if (result.ok) {
            this.publishAuthority('Shared toolingd/LSP diagnostics and code actions are authoritative', 'toolingd-lsp');
            return;
        }
        this.publishAuthority(result.message);
    }

    private publishAuthority(reason: string, authority: KpfSemanticAuthority = 'syntax-only-fallback'): void {
        this.authority = authority;
        this.options.onAuthorityChanged?.(authority, reason);
    }
}
