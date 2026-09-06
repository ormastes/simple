"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
const assert = __importStar(require("assert"));
const kpf_1 = require("../../kpf");
const canonicalToolingConformance_1 = require("../support/canonicalToolingConformance");
function admission(providerId = 'simple.language') {
    return {
        providerId,
        generation: 'generation-7',
        placement: 'worker',
        capabilities: [{ id: 'ide.language-session', major: 1 }],
        schemaDigest: 'sha256:language-v1',
        admitted: true,
    };
}
suite('KPF VS Code projection', () => {
    test('desktop adapter consumes the canonical receipt and snapshot corpus', async () => {
        const corpus = await (0, canonicalToolingConformance_1.loadCanonicalToolingConformanceV1)();
        const accepted = [];
        const session = new kpf_1.KpfToolingSession((batch) => accepted.push(batch.canonicalResultId));
        session.admit(admission());
        session.openSnapshot({ uri: corpus.uri, version: corpus.revision, digest: corpus.content_digest });
        assert.strictEqual(session.acceptDiagnostics({
            snapshot: { uri: corpus.uri, version: corpus.revision, digest: corpus.content_digest },
            canonicalResultId: corpus.canonical_result_id,
            diagnostics: [{ message: 'broken' }],
            semanticCoverageComplete: corpus.semantic_coverage_complete,
        }), true);
        assert.deepStrictEqual(accepted, [corpus.canonical_result_id]);
        assert.strictEqual(session.getStatus().semanticClean, false);
    });
    test('degraded results never claim semantic clean', () => {
        const published = [];
        const session = new kpf_1.KpfToolingSession((batch) => published.push(batch));
        session.admit(admission());
        session.openSnapshot({ uri: 'file:///main.spl', version: 1, digest: 'one' });
        session.markDegraded('syntax fallback only');
        assert.strictEqual(session.acceptDiagnostics({
            snapshot: { uri: 'file:///main.spl', version: 1, digest: 'one' },
            canonicalResultId: 'kpf-result-v1:partial:11:12',
            diagnostics: [],
            semanticCoverageComplete: false,
        }), true);
        assert.deepStrictEqual(session.getStatus(), {
            state: 'Degraded',
            semanticClean: false,
            reason: 'syntax fallback only',
            admission: admission(),
        });
        assert.strictEqual(published.length, 1);
    });
    test('rejects diagnostics for stale snapshots', () => {
        let publishCount = 0;
        const session = new kpf_1.KpfToolingSession(() => { publishCount += 1; });
        session.admit(admission());
        session.openSnapshot({ uri: 'file:///main.spl', version: 1, digest: 'one' });
        session.openSnapshot({ uri: 'file:///main.spl', version: 2, digest: 'two' });
        assert.strictEqual(session.acceptDiagnostics({
            snapshot: { uri: 'file:///main.spl', version: 1, digest: 'one' },
            canonicalResultId: 'kpf-result-v1:complete-clean:11:12',
            diagnostics: [],
            semanticCoverageComplete: true,
        }), false);
        assert.strictEqual(publishCount, 0);
        assert.strictEqual(session.getStatus().semanticClean, false);
    });
    test('preserves canonical result identity and cleans snapshots on disconnect', () => {
        const cancelled = [];
        const accepted = [];
        const session = new kpf_1.KpfToolingSession((batch) => accepted.push(batch.canonicalResultId), (snapshot) => cancelled.push(`${snapshot.uri}@${snapshot.version}`));
        session.admit(admission());
        session.openSnapshot({ uri: 'file:///main.spl', version: 1, digest: 'one' });
        session.openSnapshot({ uri: 'file:///main.spl', version: 2, digest: 'two' });
        const canonicalResultId = 'kpf-result-v1:complete-clean:11:12:13:14:21:22:23:24:1:1:0';
        assert.strictEqual(session.acceptDiagnostics({
            snapshot: { uri: 'file:///main.spl', version: 2, digest: 'two' },
            canonicalResultId,
            diagnostics: [],
            semanticCoverageComplete: true,
        }), true);
        session.disconnect('client disconnected');
        assert.deepStrictEqual(accepted, [canonicalResultId]);
        assert.deepStrictEqual(cancelled, ['file:///main.spl@1', 'file:///main.spl@2']);
        assert.strictEqual(session.getStatus().state, 'Unavailable');
        assert.strictEqual(session.acceptDiagnostics({
            snapshot: { uri: 'file:///main.spl', version: 2, digest: 'two' },
            canonicalResultId,
            diagnostics: [],
            semanticCoverageComplete: true,
        }), false);
    });
    test('rejects a mutated noncanonical result identity', () => {
        let publishCount = 0;
        const session = new kpf_1.KpfToolingSession(() => { publishCount += 1; });
        session.admit(admission());
        session.openSnapshot({ uri: 'file:///main.spl', version: 1, digest: 'one' });
        assert.strictEqual(session.acceptDiagnostics({
            snapshot: { uri: 'file:///main.spl', version: 1, digest: 'one' },
            canonicalResultId: 'mutated-result',
            diagnostics: [],
            semanticCoverageComplete: true,
        }), false);
        assert.strictEqual(publishCount, 0);
        assert.strictEqual(session.getStatus().semanticClean, false);
    });
    test('starts only the worker selected by language activation', async () => {
        const starts = [];
        const client = new kpf_1.KpfWorkerClient([
            { languageId: 'simple', providerId: 'simple.language' },
            { languageId: 'rust', providerId: 'rust.language' },
            { languageId: 'cpp', providerId: 'cpp.language' },
        ], {
            start: async (providerId) => {
                starts.push(providerId);
                return { admission: admission(providerId), stop: async () => undefined };
            },
        });
        await client.activateLanguage('simple');
        await client.activateLanguage('simple');
        assert.deepStrictEqual(starts, ['simple.language']);
        assert.deepStrictEqual(client.startedProviderIds(), ['simple.language']);
        await client.dispose();
    });
    test('filters generated commands by admitted capabilities', () => {
        const withoutLanguage = (0, kpf_1.projectContributionCommands)(kpf_1.GENERATED_KPF_CONTRIBUTIONS, new Set());
        const withLanguage = (0, kpf_1.projectContributionCommands)(kpf_1.GENERATED_KPF_CONTRIBUTIONS, new Set(['ide.language-session']));
        assert.strictEqual(withoutLanguage.some((entry) => entry.command === 'simple.lsp.restart'), false);
        assert.strictEqual(withLanguage.some((entry) => entry.command === 'simple.lsp.restart'), true);
    });
    test('starts tooling only after the selected language is observed', async () => {
        const starts = [];
        const cutover = new kpf_1.KpfProductionCutover({
            languageId: 'simple',
            isWorkspaceTrusted: () => true,
            resolvePlacement: () => 'native-process',
            bootstrap: async (resolveFrom) => {
                starts.push(resolveFrom);
                return { ok: true, message: 'ready' };
            },
            restart: async () => ({ ok: true, message: 'restarted' }),
        });
        assert.strictEqual(cutover.observeLanguage('rust', '/workspace/lib.rs'), undefined);
        await cutover.observeLanguage('simple', '/workspace/main.spl');
        await cutover.observeLanguage('simple', '/workspace/other.spl');
        assert.deepStrictEqual(starts, ['/workspace/main.spl']);
        assert.strictEqual(cutover.semanticAuthority(), 'toolingd-lsp');
    });
    test('trust-gates process placement while retaining explicit syntax fallback', async () => {
        let trusted = false;
        let starts = 0;
        const authorities = [];
        const cutover = new kpf_1.KpfProductionCutover({
            languageId: 'simple',
            isWorkspaceTrusted: () => trusted,
            resolvePlacement: () => 'worker-process',
            bootstrap: async () => {
                starts += 1;
                return { ok: true, message: 'ready' };
            },
            restart: async () => ({ ok: true, message: 'restarted' }),
            onAuthorityChanged: (authority) => authorities.push(authority),
        });
        const blocked = await cutover.observeLanguage('simple', '/workspace/main.spl');
        assert.strictEqual(blocked?.ok, false);
        assert.strictEqual(starts, 0);
        assert.strictEqual(cutover.semanticAuthority(), 'syntax-only-fallback');
        trusted = true;
        await cutover.workspaceTrustGranted();
        assert.strictEqual(starts, 1);
        assert.strictEqual(cutover.semanticAuthority(), 'toolingd-lsp');
        assert.deepStrictEqual(authorities, ['syntax-only-fallback', 'syntax-only-fallback', 'toolingd-lsp']);
    });
    test('allows sandboxed wasm tooling without workspace trust', async () => {
        let starts = 0;
        const cutover = new kpf_1.KpfProductionCutover({
            languageId: 'simple',
            isWorkspaceTrusted: () => false,
            resolvePlacement: () => 'wasm',
            bootstrap: async () => {
                starts += 1;
                return { ok: true, message: 'ready' };
            },
            restart: async () => ({ ok: true, message: 'restarted' }),
        });
        await cutover.observeLanguage('simple', 'file:///main.spl');
        assert.strictEqual(starts, 1);
        assert.strictEqual(cutover.semanticAuthority(), 'toolingd-lsp');
    });
});
//# sourceMappingURL=kpfProjection.test.js.map