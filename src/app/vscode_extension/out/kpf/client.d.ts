import { KpfAdmissionMetadata } from './types';
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
export declare class KpfWorkerClient {
    private readonly launcher;
    private readonly sessions;
    private readonly routeByLanguage;
    constructor(routes: readonly KpfLanguageRoute[], launcher: KpfWorkerLauncher);
    activateLanguage(languageId: string): Promise<KpfWorkerSession | undefined>;
    startedProviderIds(): readonly string[];
    dispose(): Promise<void>;
}
export interface KpfLspClientFacade {
    activateLanguage(languageId: string): Promise<KpfWorkerSession | undefined>;
    dispose(): Promise<void>;
}
export declare function createKpfLspClientFacade(routes: readonly KpfLanguageRoute[], launcher: KpfWorkerLauncher): KpfLspClientFacade;
