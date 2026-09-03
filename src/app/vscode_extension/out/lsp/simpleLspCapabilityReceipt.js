"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.authoritativeLspReceipt = authoritativeLspReceipt;
exports.degradedLspReceipt = degradedLspReceipt;
exports.publishLspCapabilityReceipt = publishLspCapabilityReceipt;
function authoritativeLspReceipt(source) {
    return {
        authority: 'authoritative',
        coverage: 'semantic',
        source,
        fallbackActive: false,
        message: `Simple LSP server running (${source}); semantic results are authoritative`,
    };
}
function degradedLspReceipt(message, detail) {
    return {
        authority: 'degraded',
        coverage: 'syntax-only',
        source: 'fallback',
        fallbackActive: true,
        message: `${message}; local fallback coverage is syntax-only and is not a semantic-clean result`,
        detail,
    };
}
function publishLspCapabilityReceipt(services, controls, receipt) {
    for (const control of controls) {
        control.setEnabled(receipt.fallbackActive);
    }
    if (receipt.authority === 'authoritative') {
        services.markReady('lsp', receipt.message, receipt.source);
        for (const service of ['diagnostics', 'symbols', 'semanticTokens']) {
            services.markReady(service, 'Provided by the authoritative Simple LSP session', receipt.source);
        }
        return;
    }
    services.markDegraded('lsp', receipt.message, 'fallback', receipt.detail);
    const fallbackStatus = {
        health: 'degraded',
        source: 'fallback',
        message: 'Local syntax-only fallback active; semantic completeness is unavailable',
        lastError: receipt.detail,
    };
    for (const service of ['diagnostics', 'symbols', 'semanticTokens']) {
        services.setStatus(service, fallbackStatus);
    }
}
//# sourceMappingURL=simpleLspCapabilityReceipt.js.map