import { KpfAdmissionMetadata, KpfDiagnosticBatch, KpfServiceStatus, KpfSnapshot } from './types';
export type DiagnosticPublisher<T> = (batch: KpfDiagnosticBatch<T>) => void;
export type SnapshotCancellation = (snapshot: KpfSnapshot) => void;
export declare class KpfToolingSession<T> {
    private readonly publishDiagnostics;
    private readonly cancelSnapshot;
    private readonly snapshots;
    private status;
    constructor(publishDiagnostics: DiagnosticPublisher<T>, cancelSnapshot?: SnapshotCancellation);
    admit(metadata: KpfAdmissionMetadata): void;
    markDegraded(reason: string): void;
    markUnavailable(reason: string): void;
    openSnapshot(snapshot: KpfSnapshot): void;
    closeSnapshot(uri: string): boolean;
    disconnect(reason?: string): void;
    acceptDiagnostics(batch: KpfDiagnosticBatch<T>): boolean;
    getStatus(): KpfServiceStatus;
}
