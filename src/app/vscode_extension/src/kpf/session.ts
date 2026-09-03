import {
    KpfAdmissionMetadata,
    KpfDiagnosticBatch,
    KpfServiceStatus,
    KpfSnapshot,
    validateAdmission,
} from './types';

export type DiagnosticPublisher<T> = (batch: KpfDiagnosticBatch<T>) => void;

export class KpfToolingSession<T> {
    private readonly snapshots = new Map<string, KpfSnapshot>();
    private status: KpfServiceStatus = {
        state: 'Unavailable',
        semanticClean: false,
        reason: 'No admitted language provider',
    };

    public constructor(private readonly publishDiagnostics: DiagnosticPublisher<T>) {}

    public admit(metadata: KpfAdmissionMetadata): void {
        validateAdmission(metadata);
        this.status = {
            state: 'Authoritative',
            semanticClean: false,
            admission: metadata,
        };
    }

    public markDegraded(reason: string): void {
        this.status = {
            state: 'Degraded',
            semanticClean: false,
            reason,
            admission: this.status.admission,
        };
    }

    public markUnavailable(reason: string): void {
        this.status = {
            state: 'Unavailable',
            semanticClean: false,
            reason,
        };
    }

    public openSnapshot(snapshot: KpfSnapshot): void {
        const current = this.snapshots.get(snapshot.uri);
        if (current && snapshot.version <= current.version) {
            throw new Error(`Snapshot version must advance for ${snapshot.uri}`);
        }
        this.snapshots.set(snapshot.uri, snapshot);
    }

    public acceptDiagnostics(batch: KpfDiagnosticBatch<T>): boolean {
        const current = this.snapshots.get(batch.snapshot.uri);
        if (!current || current.version !== batch.snapshot.version || current.digest !== batch.snapshot.digest) {
            return false;
        }

        if (this.status.state !== 'Authoritative' || !batch.semanticCoverageComplete) {
            this.status = {
                ...this.status,
                state: this.status.state === 'Unavailable' ? 'Unavailable' : 'Degraded',
                semanticClean: false,
                reason: this.status.reason ?? 'Semantic coverage is incomplete',
            };
        } else {
            this.status = {
                ...this.status,
                semanticClean: batch.diagnostics.length === 0,
                reason: undefined,
            };
        }

        this.publishDiagnostics(batch);
        return true;
    }

    public getStatus(): KpfServiceStatus {
        return this.status;
    }
}
