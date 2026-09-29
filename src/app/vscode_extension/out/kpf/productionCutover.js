"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.KpfProductionCutover = void 0;
class KpfProductionCutover {
    constructor(options) {
        this.options = options;
        this.languageObserved = false;
        this.authority = 'syntax-only-fallback';
        this.publishAuthority('Syntax-only fallback active until the shared tooling service is admitted');
    }
    observeLanguage(languageId, resolveFrom) {
        if (languageId !== this.options.languageId) {
            return undefined;
        }
        this.languageObserved = true;
        this.observedResolveFrom = resolveFrom ?? this.observedResolveFrom;
        return this.ensureAuthoritative();
    }
    workspaceTrustGranted() {
        if (!this.languageObserved) {
            return undefined;
        }
        return this.ensureAuthoritative();
    }
    async restart() {
        const blocked = this.trustFailure();
        if (blocked) {
            this.publishAuthority(blocked.message);
            return blocked;
        }
        const result = await this.options.restart();
        this.applyResult(result);
        return result;
    }
    semanticAuthority() {
        return this.authority;
    }
    ensureAuthoritative() {
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
                .catch((error) => {
                const result = {
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
    trustFailure() {
        const placement = this.options.resolvePlacement();
        if (placement === 'wasm' || this.options.isWorkspaceTrusted()) {
            return undefined;
        }
        return {
            ok: false,
            message: `Workspace trust is required for ${placement}; syntax-only fallback remains active`,
        };
    }
    applyResult(result) {
        if (result.ok) {
            this.publishAuthority('Shared toolingd/LSP diagnostics and code actions are authoritative', 'toolingd-lsp');
            return;
        }
        this.publishAuthority(result.message);
    }
    publishAuthority(reason, authority = 'syntax-only-fallback') {
        this.authority = authority;
        this.options.onAuthorityChanged?.(authority, reason);
    }
}
exports.KpfProductionCutover = KpfProductionCutover;
//# sourceMappingURL=productionCutover.js.map