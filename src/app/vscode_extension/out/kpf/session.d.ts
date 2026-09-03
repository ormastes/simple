import { KpfAdmissionMetadata, KpfDiagnosticBatch, KpfServiceStatus, KpfSnapshot } from './types';
export type DiagnosticPublisher<T> = (batch: KpfDiagnosticBatch<T>) => void;
export declare class KpfToolingSession<T> {
    private readonly publishDiagnostics;
    private readonly snapshots;
    private status;
    constructor(publishDiagnostics: DiagnosticPublisher<T>);
    admit(metadata: KpfAdmissionMetadata): void;
    markDegraded(reason: string): void;
    markUnavailable(reason: string): void;
    openSnapshot(snapshot: KpfSnapshot): void;
    acceptDiagnostics(batch: KpfDiagnosticBatch<T>): boolean;
    getStatus(): KpfServiceStatus;
}
