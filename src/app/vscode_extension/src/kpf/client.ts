import { KpfAdmissionMetadata, validateAdmission } from './types';

export interface KpfWorkerSession {
    readonly admission: KpfAdmissionMetadata;
    stop(): Promise<void>;
}

export interface KpfWorkerLauncher {
    start(providerId: string): Promise<KpfWorkerSession>;
}

export interface KpfLanguageRoute {
    readonly languageId: string;
    readonly providerId: string;
}

export class KpfWorkerClient {
    private readonly sessions = new Map<string, Promise<KpfWorkerSession>>();
    private readonly routeByLanguage: ReadonlyMap<string, KpfLanguageRoute>;

    public constructor(routes: readonly KpfLanguageRoute[], private readonly launcher: KpfWorkerLauncher) {
        this.routeByLanguage = new Map(routes.map((route) => [route.languageId, route]));
    }

    public async activateLanguage(languageId: string): Promise<KpfWorkerSession | undefined> {
        const route = this.routeByLanguage.get(languageId);
        if (!route) {
            return undefined;
        }
        let session = this.sessions.get(route.providerId);
        if (!session) {
            session = this.launcher.start(route.providerId).then((started) => {
                validateAdmission(started.admission);
                if (started.admission.providerId !== route.providerId) {
                    throw new Error(`Worker admitted as ${started.admission.providerId}, expected ${route.providerId}`);
                }
                if (started.admission.placement !== 'worker' && started.admission.placement !== 'wasm') {
                    throw new Error(`Invalid language worker placement ${started.admission.placement}`);
                }
                return started;
            });
            this.sessions.set(route.providerId, session);
        }
        return session;
    }

    public startedProviderIds(): readonly string[] {
        return [...this.sessions.keys()].sort();
    }

    public async dispose(): Promise<void> {
        const sessions = await Promise.allSettled(this.sessions.values());
        this.sessions.clear();
        await Promise.all(sessions.flatMap((result) => (
            result.status === 'fulfilled' ? [result.value.stop()] : []
        )));
    }
}

export interface KpfLspClientFacade {
    activateLanguage(languageId: string): Promise<KpfWorkerSession | undefined>;
    dispose(): Promise<void>;
}

export function createKpfLspClientFacade(
    routes: readonly KpfLanguageRoute[],
    launcher: KpfWorkerLauncher,
): KpfLspClientFacade {
    return new KpfWorkerClient(routes, launcher);
}
