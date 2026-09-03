import type { ExtensionHostServices, ServiceStatus } from '../services/extensionHostServices';

export type SimpleLspAuthority = 'authoritative' | 'degraded';
export type SimpleLspCoverage = 'semantic' | 'syntax-only';
export type SimpleLspSource = 'native' | 'wasm' | 'fallback';

export interface SimpleLspCapabilityReceipt {
    authority: SimpleLspAuthority;
    coverage: SimpleLspCoverage;
    source: SimpleLspSource;
    fallbackActive: boolean;
    message: string;
    detail?: string;
}

export interface SimpleLspFallbackControl {
    setEnabled(enabled: boolean): void;
}

export function authoritativeLspReceipt(source: Exclude<SimpleLspSource, 'fallback'>): SimpleLspCapabilityReceipt {
    return {
        authority: 'authoritative',
        coverage: 'semantic',
        source,
        fallbackActive: false,
        message: `Simple LSP server running (${source}); semantic results are authoritative`,
    };
}

export function degradedLspReceipt(message: string, detail?: string): SimpleLspCapabilityReceipt {
    return {
        authority: 'degraded',
        coverage: 'syntax-only',
        source: 'fallback',
        fallbackActive: true,
        message: `${message}; local fallback coverage is syntax-only and is not a semantic-clean result`,
        detail,
    };
}

export function publishLspCapabilityReceipt(
    services: ExtensionHostServices,
    controls: readonly SimpleLspFallbackControl[],
    receipt: SimpleLspCapabilityReceipt,
): void {
    for (const control of controls) {
        control.setEnabled(receipt.fallbackActive);
    }

    if (receipt.authority === 'authoritative') {
        services.markReady('lsp', receipt.message, receipt.source);
        for (const service of ['diagnostics', 'symbols', 'semanticTokens'] as const) {
            services.markReady(service, 'Provided by the authoritative Simple LSP session', receipt.source);
        }
        return;
    }

    services.markDegraded('lsp', receipt.message, 'fallback', receipt.detail);
    const fallbackStatus: ServiceStatus = {
        health: 'degraded',
        source: 'fallback',
        message: 'Local syntax-only fallback active; semantic completeness is unavailable',
        lastError: receipt.detail,
    };
    for (const service of ['diagnostics', 'symbols', 'semanticTokens'] as const) {
        services.setStatus(service, fallbackStatus);
    }
}
