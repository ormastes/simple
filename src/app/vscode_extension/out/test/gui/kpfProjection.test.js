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
    test('degraded results never claim semantic clean', () => {
        const published = [];
        const session = new kpf_1.KpfToolingSession((batch) => published.push(batch));
        session.admit(admission());
        session.openSnapshot({ uri: 'file:///main.spl', version: 1, digest: 'one' });
        session.markDegraded('syntax fallback only');
        assert.strictEqual(session.acceptDiagnostics({
            snapshot: { uri: 'file:///main.spl', version: 1, digest: 'one' },
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
});
//# sourceMappingURL=kpfProjection.test.js.map