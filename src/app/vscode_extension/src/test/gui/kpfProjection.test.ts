import * as assert from 'assert';
import {
    GENERATED_KPF_CONTRIBUTIONS,
    KpfAdmissionMetadata,
    KpfToolingSession,
    KpfProductionCutover,
    KpfWorkerClient,
    KpfWorkerSession,
    projectContributionCommands,
} from '../../kpf';
import { loadCanonicalToolingConformanceV1 } from '../support/canonicalToolingConformance';

function admission(providerId = 'simple.language'): KpfAdmissionMetadata {
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
        const corpus = await loadCanonicalToolingConformanceV1();
        const accepted: string[] = [];
        const session = new KpfToolingSession((batch) => accepted.push(batch.canonicalResultId));
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
        const published: unknown[] = [];
        const session = new KpfToolingSession((batch) => published.push(batch));
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
        const session = new KpfToolingSession(() => { publishCount += 1; });
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
        const cancelled: string[] = [];
        const accepted: string[] = [];
        const session = new KpfToolingSession(
            (batch) => accepted.push(batch.canonicalResultId),
            (snapshot) => cancelled.push(`${snapshot.uri}@${snapshot.version}`),
        );
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
        const session = new KpfToolingSession(() => { publishCount += 1; });
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
        const starts: string[] = [];
        const client = new KpfWorkerClient([
            { languageId: 'simple', providerId: 'simple.language' },
            { languageId: 'rust', providerId: 'rust.language' },
            { languageId: 'cpp', providerId: 'cpp.language' },
        ], {
            start: async (providerId: string): Promise<KpfWorkerSession> => {
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
        const withoutLanguage = projectContributionCommands(GENERATED_KPF_CONTRIBUTIONS, new Set());
        const withLanguage = projectContributionCommands(
            GENERATED_KPF_CONTRIBUTIONS,
            new Set(['ide.language-session']),
        );

        assert.strictEqual(withoutLanguage.some((entry) => entry.command === 'simple.lsp.restart'), false);
        assert.strictEqual(withLanguage.some((entry) => entry.command === 'simple.lsp.restart'), true);
    });

    test('starts tooling only after the selected language is observed', async () => {
        const starts: Array<string | undefined> = [];
        const cutover = new KpfProductionCutover({
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
        const authorities: string[] = [];
        const cutover = new KpfProductionCutover({
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
        const cutover = new KpfProductionCutover({
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
