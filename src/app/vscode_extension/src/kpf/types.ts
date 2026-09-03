export type KpfPlacement = 'static' | 'native' | 'worker' | 'wasm';

export type KpfServiceState = 'Authoritative' | 'Degraded' | 'Unavailable';

export interface KpfCapability {
    readonly id: string;
    readonly major: number;
}

export interface KpfAdmissionMetadata {
    readonly providerId: string;
    readonly generation: string;
    readonly placement: KpfPlacement;
    readonly capabilities: readonly KpfCapability[];
    readonly schemaDigest: string;
    readonly admitted: boolean;
}

export interface KpfSnapshot {
    readonly uri: string;
    readonly version: number;
    readonly digest: string;
}

export interface KpfDiagnosticBatch<T> {
    readonly snapshot: KpfSnapshot;
    readonly canonicalResultId: string;
    readonly diagnostics: readonly T[];
    readonly semanticCoverageComplete: boolean;
}

export interface KpfServiceStatus {
    readonly state: KpfServiceState;
    readonly semanticClean: boolean;
    readonly reason?: string;
    readonly admission?: KpfAdmissionMetadata;
}

export function validateAdmission(metadata: KpfAdmissionMetadata): void {
    if (!metadata.admitted) {
        throw new Error(`Provider ${metadata.providerId} is not admitted`);
    }
    if (!metadata.providerId || !metadata.generation || !metadata.schemaDigest) {
        throw new Error('Admitted provider metadata is incomplete');
    }
    const capabilityKeys = new Set<string>();
    for (const capability of metadata.capabilities) {
        if (!capability.id || capability.major < 1) {
            throw new Error('Invalid admitted capability');
        }
        const key = `${capability.id}@${capability.major}`;
        if (capabilityKeys.has(key)) {
            throw new Error(`Duplicate admitted capability ${key}`);
        }
        capabilityKeys.add(key);
    }
}
