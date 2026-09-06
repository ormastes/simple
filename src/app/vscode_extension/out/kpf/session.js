"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.KpfToolingSession = void 0;
const types_1 = require("./types");
class KpfToolingSession {
    constructor(publishDiagnostics, cancelSnapshot = () => undefined) {
        this.publishDiagnostics = publishDiagnostics;
        this.cancelSnapshot = cancelSnapshot;
        this.snapshots = new Map();
        this.status = {
            state: 'Unavailable',
            semanticClean: false,
            reason: 'No admitted language provider',
        };
    }
    admit(metadata) {
        (0, types_1.validateAdmission)(metadata);
        this.status = {
            state: 'Authoritative',
            semanticClean: false,
            admission: metadata,
        };
    }
    markDegraded(reason) {
        this.status = {
            state: 'Degraded',
            semanticClean: false,
            reason,
            admission: this.status.admission,
        };
    }
    markUnavailable(reason) {
        this.status = {
            state: 'Unavailable',
            semanticClean: false,
            reason,
        };
    }
    openSnapshot(snapshot) {
        const current = this.snapshots.get(snapshot.uri);
        if (current && snapshot.version <= current.version) {
            throw new Error(`Snapshot version must advance for ${snapshot.uri}`);
        }
        if (current) {
            this.cancelSnapshot(current);
        }
        this.snapshots.set(snapshot.uri, snapshot);
    }
    closeSnapshot(uri) {
        const current = this.snapshots.get(uri);
        if (!current) {
            return false;
        }
        this.cancelSnapshot(current);
        this.snapshots.delete(uri);
        return true;
    }
    disconnect(reason = 'Tooling connection closed') {
        for (const snapshot of this.snapshots.values()) {
            this.cancelSnapshot(snapshot);
        }
        this.snapshots.clear();
        this.markUnavailable(reason);
    }
    acceptDiagnostics(batch) {
        if (!batch.canonicalResultId.startsWith('kpf-result-v1:')) {
            return false;
        }
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
        }
        else {
            this.status = {
                ...this.status,
                semanticClean: batch.diagnostics.length === 0,
                reason: undefined,
            };
        }
        this.publishDiagnostics(batch);
        return true;
    }
    getStatus() {
        return this.status;
    }
}
exports.KpfToolingSession = KpfToolingSession;
//# sourceMappingURL=session.js.map