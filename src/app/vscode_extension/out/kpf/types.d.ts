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
export declare function validateAdmission(metadata: KpfAdmissionMetadata): void;
