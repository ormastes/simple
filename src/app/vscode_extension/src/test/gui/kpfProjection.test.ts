import * as assert from 'assert';
import {
    GENERATED_KPF_CONTRIBUTIONS,
    KpfAdmissionMetadata,
    KpfToolingSession,
    KpfWorkerClient,
    KpfWorkerSession,
    projectContributionCommands,
} from '../../kpf';

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
    test('degraded results never claim semantic clean', () => {
        const published: unknown[] = [];
        const session = new KpfToolingSession((batch) => published.push(batch));
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
        const session = new KpfToolingSession(() => { publishCount += 1; });
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
});
